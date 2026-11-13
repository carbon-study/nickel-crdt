//! Retained facts and a rebuilt FugueMax tree. This is deliberately not an
//! incremental index. The external caller fences each writer to one producer.
#[derive(Clone, Copy, Debug, Eq, PartialOrd, Ord)]
pub enum Writer {
    Alice,
    Bo,
}
fn writer_index(w: Writer) -> u8 {
    match w {
        Writer::Alice => 0,
        Writer::Bo => 1,
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialOrd, Ord)]
pub struct EventId {
    pub writer: Writer,
    pub counter: u64,
}
#[derive(Clone, Copy, Debug, Eq, PartialOrd, Ord)]
pub struct BirthId {
    pub event: EventId,
    pub index: usize,
}
#[derive(Clone, Debug, Eq)]
pub struct Fact {
    pub id: EventId,
    pub after: Vec<EventId>,
    pub insert: Vec<u32>,
    pub delete: Vec<BirthId>,
    pub gap: Option<usize>,
}


#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Invalid {
    Counter,
    Conflict,
    DependencyDuplicate,
    Predecessor,
    DeleteDuplicate,
    DeleteNotVisible,
    Scalar,
    Gap,
    PlacementWithoutBirth,
    NoWriter,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Capacity {
    Counter,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Invalid(Invalid),
    Missing,
    Capacity(Capacity),
    Internal,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Admission {
    Added,
    Duplicate,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Local {
    Empty,
    Authored(Fact),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Side {
    Left,
    Right,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Node {
    pub id: BirthId,
    pub scalar: u32,
    pub left_origin: Option<BirthId>,
    pub right_origin: Option<BirthId>,
    pub parent: Option<BirthId>,
    pub side: Side,
    left: Vec<BirthId>,
    right: Vec<BirthId>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Tree {
    nodes: Vec<Node>,
    root_right: Vec<BirthId>,
}
#[derive(Clone, Copy)]
enum Visit {
    Enter(BirthId),
    Emit(BirthId),
}
impl PartialEq for Writer {
    fn eq(&self, other: &Self) -> bool {
        writer_index(*self) == writer_index(*other)
    }
}
impl PartialEq for EventId {
    fn eq(&self, other: &Self) -> bool {
        self.writer == other.writer && self.counter == other.counter
    }
}
impl PartialEq for BirthId {
    fn eq(&self, other: &Self) -> bool {
        self.event == other.event && self.index == other.index
    }
}
// Keep identity-critical comparison as an ordinary call: the pinned F* backend
// lowers PartialEq operator calls directly to structural equality.
fn fact_equal(left: &Fact, right: &Fact) -> bool {
    left.id == right.id
        && left.after == right.after
        && left.insert == right.insert
        && left.delete == right.delete
        && left.gap == right.gap
}
impl PartialEq for Fact {
    fn eq(&self, other: &Self) -> bool {
        fact_equal(self, other)
    }
}
fn event_lt(a: EventId, b: EventId) -> bool {
    writer_index(a.writer) < writer_index(b.writer)
        || (a.writer == b.writer && a.counter < b.counter)
}
fn birth_lt(a: BirthId, b: BirthId) -> bool {
    event_lt(a.event, b.event) || (a.event == b.event && a.index < b.index)
}
const MAX_COUNTER: u64 = 9_007_199_254_740_991;
fn invalid(reason: Invalid) -> Error {
    Error::Invalid(reason)
}
// Indexed so the extracted loop has an executable range semantics at this pin.
fn validate_scalars(scalars: &[u32]) -> Result<(), Error> {
    for i in 0..scalars.len() {
        let scalar = scalars[i];
        if scalar > 0x10ffff || (scalar >= 0xd800 && scalar <= 0xdfff) {
            return Err(invalid(Invalid::Scalar));
        }
    }
    Ok(())
}
fn duplicate_events(xs: &[EventId]) -> bool {
    crate::event_layer::duplicate_ids(xs, &TEXT_OPS.0)
}
fn duplicate_births(xs: &[BirthId]) -> bool {
    for i in 0..xs.len() {
        for j in 0..i {
            if xs[i] == xs[j] {
                return true;
            }
        }
    }
    false
}
impl Default for Tree {
    fn default() -> Self {
        Self {
            nodes: Vec::new(),
            root_right: Vec::new(),
        }
    }
}
fn add(a: usize, b: usize) -> Result<usize, Error> {
    if b > usize::MAX - a {
        return Err(Error::Internal);
    }
    Ok(a + b)
}
fn push<T>(xs: &mut Vec<T>, value: T) -> Result<(), Error> {
    crate::event_layer::push(xs, value, internal_error)
}
fn insert<T>(xs: &mut Vec<T>, at: usize, value: T) -> Result<(), Error> {
    if at > xs.len() || xs.len() == usize::MAX {
        return Err(Error::Internal);
    }
    xs.insert(at, value);
    Ok(())
}
impl Tree {
    fn position(&self, id: BirthId) -> Result<usize, Error> {
        for i in 0..self.nodes.len() {
            if self.nodes[i].id == id {
                return Ok(i);
            }
        }
        Err(Error::Internal)
    }
    fn node(&self, id: BirthId) -> Result<Node, Error> {
        let p = self.position(id)?;
        if p >= self.nodes.len() {
            return Err(Error::Internal);
        }
        Ok(self.nodes[p].clone())
    }
    fn whole(&self) -> Result<Vec<BirthId>, Error> {
        // Real representation overflow for the two visits per retained node.
        if self.nodes.len() > usize::MAX / 2 { return Err(Error::Internal); }
        let mut stack = Vec::new();
        let mut out = Vec::new();
        for offset in 0..self.root_right.len() {
            let i = self.root_right.len() - 1 - offset;
            push(&mut stack, Visit::Enter(self.root_right[i]))?;
        }
        // Exactly one Enter and Emit per retained node; no recursive stack.
        for _ in 0..self.nodes.len() * 2 {
            let visit = stack.pop().ok_or(Error::Internal)?;
            match visit {
                Visit::Emit(id) => push(&mut out, id)?,
                Visit::Enter(id) => {
                    let node = self.node(id)?;
                    for offset in 0..node.right.len() {
                        let i = node.right.len() - 1 - offset;
                        push(&mut stack, Visit::Enter(node.right[i]))?;
                    }
                    push(&mut stack, Visit::Emit(id))?;
                    for offset in 0..node.left.len() {
                        let i = node.left.len() - 1 - offset;
                        push(&mut stack, Visit::Enter(node.left[i]))?;
                    }
                }
            }
        }
        if !stack.is_empty() {
            return Err(Error::Internal);
        }
        Ok(out)
    }
    fn rank(order: &[BirthId], origin: Option<BirthId>) -> Result<usize, Error> {
        if let Some(id) = origin {
            for i in 0..order.len() {
                if order[i] == id {
                    return Ok(i);
                }
            }
            Err(Error::Internal)
        } else {
            Ok(usize::MAX)
        }
    }
    fn add(&mut self, mut node: Node) -> Result<(), Error> {
        for old in self.nodes.iter() {
            if old.id == node.id {
                return Err(Error::Internal);
            }
        }
        let whole = self.whole()?;
        let parent = match node.parent {
            Some(id) => Some(self.position(id)?),
            None => None,
        };
        let siblings = match parent {
            Some(p) => {
                if p >= self.nodes.len() {
                    return Err(Error::Internal);
                }
                match node.side {
                    Side::Left => self.nodes[p].left.clone(),
                    Side::Right => self.nodes[p].right.clone(),
                }
            }
            None => {
                if !matches!(node.side, Side::Right) {
                    return Err(Error::Internal);
                }
                self.root_right.clone()
            }
        };
        let mut at = siblings.len();
        let rank = Self::rank(&whole, node.right_origin)?;
        for i in 0..siblings.len() {
            let old = self.node(siblings[i])?;
            let before = if matches!(node.side, Side::Right) {
                rank > Self::rank(&whole, old.right_origin)?
                    || (node.right_origin == old.right_origin && birth_lt(node.id, old.id))
            } else {
                birth_lt(node.id, old.id)
            };
            if before {
                at = i;
                break;
            }
        }
        match parent {
            Some(p) => {
                if p >= self.nodes.len() {
                    return Err(Error::Internal);
                }
                match node.side {
                    Side::Left => insert(&mut self.nodes[p].left, at, node.id)?,
                    Side::Right => insert(&mut self.nodes[p].right, at, node.id)?,
                }
            }
            None => insert(&mut self.root_right, at, node.id)?,
        }
        node.left = Vec::new();
        node.right = Vec::new();
        push(&mut self.nodes, node)?;
        Ok(())
    }
    fn insert(
        &mut self,
        id: BirthId,
        scalar: u32,
        visible: &[BirthId],
        gap: usize,
    ) -> Result<Node, Error> {
        let all = self.whole()?;
        let mut view = Vec::new();
        for id in all.iter() {
            if has_birth(visible, *id) {
                push(&mut view, *id)?;
            }
        }
        if view.len() != visible.len() || gap > view.len() {
            return Err(Error::Internal);
        }
        let left = if gap == 0 { None } else { Some(view[gap - 1]) };
        let next = match left {
            None => 0,
            Some(x) => {
                let p = Self::rank(&all, Some(x))?;
                if p == usize::MAX {
                    return Err(Error::Internal);
                }
                p + 1
            }
        };
        let right = if next < all.len() {
            Some(all[next])
        } else {
            None
        };
        let has_right = match left {
            None => !self.root_right.is_empty(),
            Some(x) => !self.node(x)?.right.is_empty(),
        };
        let side = if has_right { Side::Left } else { Side::Right };
        let parent = if matches!(side, Side::Right) {
            left
        } else {
            right
        };
        if matches!(side, Side::Left) && parent.is_none() {
            return Err(Error::Internal);
        }
        let node = Node {
            id,
            scalar,
            left_origin: left,
            right_origin: right,
            parent,
            side,
            left: Vec::new(),
            right: Vec::new(),
        };
        self.add(node.clone())?;
        Ok(node)
    }
}
// Pure allocation calculation; the instance commits it only after plan succeeds.
fn next_counter_after(counter: u64) -> Result<u64, Error> {
    if counter > MAX_COUNTER {
        Err(Error::Capacity(Capacity::Counter))
    } else {
        Ok(counter + 1)
    }
}
fn has_event(ids: &[EventId], id: EventId) -> bool {
    crate::event_layer::has_id(ids, &id, &TEXT_OPS.0)
}
fn has_birth(ids: &[BirthId], id: BirthId) -> bool {
    for old in ids {
        if *old == id {
            return true;
        }
    }
    false
}
fn has_fact(facts: &[Fact], id: EventId) -> bool {
    crate::event_layer::has_fact(facts, &id, &TEXT_OPS.0)
}
// Same selection scan, separated so its fresh-choice invariant can be checked.
fn choose_unseen(facts: &[Fact], out: &[Fact]) -> Result<Option<usize>, Error> {
    crate::event_layer::choose_unseen(facts, out, &TEXT_OPS.0)
}
// Copying a selected fact is a whole-fact operation, independently of its ID.
fn clone_selected_fact(fact: &Fact) -> Fact {
    fact.clone()
}
fn canonical_step(facts: &[Fact], mut out: Vec<Fact>) -> Result<Vec<Fact>, Error> {
    crate::event_layer::canonical_step(facts, out, &TEXT_OPS.0)
}
fn canonical(facts: &[Fact]) -> Result<Vec<Fact>, Error> {
    crate::event_layer::canonical(facts, &TEXT_OPS.0)
}
fn deletes(facts: &[Fact], id: BirthId) -> bool {
    for f in facts {
        if has_birth(&f.delete, id) {
            return true;
        }
    }
    false
}
fn ready(after: &[EventId], done: &[EventId]) -> bool {
    crate::event_layer::ready(after, done, &TEXT_OPS.0)
}
// Return the first eligible stored event; interpret uses this same scan.
fn choose_ready(facts: &[Fact], done: &[EventId]) -> Option<usize> {
    crate::event_layer::choose_ready(facts, done, &TEXT_OPS.0)
}
fn frontier(facts: &[Fact]) -> Result<Vec<EventId>, Error> {
    crate::event_layer::frontier(facts, &TEXT_OPS.0)
}
// Direct predecessor admission guard, separated from closure computation.
fn validate_after(facts: &[Fact], after: &[EventId]) -> Result<(), Error> {
    crate::event_layer::validate_after(facts, after, &TEXT_OPS.0)
}
// Each layer has an indexed range so its extracted callback has executable
// LoopUtil semantics; keep expansion order and ordinary error propagation.
fn extend_past(fact: &Fact, mut selected: Vec<EventId>) -> Result<Vec<EventId>, Error> {
    crate::event_layer::extend_past(fact, selected, &TEXT_OPS.0)
}
fn past_pass(facts: &[Fact], mut selected: Vec<EventId>) -> Result<Vec<EventId>, Error> {
    crate::event_layer::past_pass(facts, selected, &TEXT_OPS.0)
}
fn past(facts: &[Fact], after: &[EventId]) -> Result<Vec<EventId>, Error> {
    crate::event_layer::past(facts, after, &TEXT_OPS.0)
}
fn visible(facts: &[Fact]) -> Result<Vec<BirthId>, Error> {
    let mut ids = Vec::new();
    for fact in facts {
        for index in 0..fact.insert.len() {
            let id = BirthId {
                event: fact.id,
                index,
            };
            if !deletes(facts, id) {
                push(&mut ids, id)?;
            }
        }
    }
    Ok(ids)
}
// Preserve storage order and whole fact values while selecting an author basis.
fn select_basis(facts: &[Fact], selected: &[EventId]) -> Result<Vec<Fact>, Error> {
    crate::event_layer::select_basis(facts, selected, &TEXT_OPS.0)
}
// The author basis boundary: exact past first, then whole-fact selection.
fn event_basis(facts: &[Fact], event: &Fact) -> Result<(Vec<EventId>, Vec<Fact>), Error> {
    crate::event_layer::event_basis(facts, event, &TEXT_OPS.0)
}
// Replay one operation group without changing its node order.
fn replay_nodes(mut tree: Tree, nodes: &[Node]) -> Result<Tree, Error> {
    for i in 0..nodes.len() {
        tree.add(nodes[i].clone())?;
    }
    Ok(tree)
}
// Reconstruct the author's tree from precisely the selected operation groups.
fn replay_author(operations: &[(EventId, Vec<Node>)], selected: &[EventId]) -> Result<Tree, Error> {
    let mut author = Tree::default();
    for i in 0..operations.len() {
        let (id, ops) = operations[i].clone();
        if has_event(selected, id) {
            author = replay_nodes(author, &ops)?;
        }
    }
    Ok(author)
}
// Finish author reconstruction before applying the event's own insertions.
fn author_context(
    facts: &[Fact],
    event: &Fact,
    operations: &[(EventId, Vec<Node>)],
) -> Result<(Vec<Fact>, Tree), Error> {
    let (selected, basis) = event_basis(facts, event)?;
    let author = replay_author(operations, &selected)?;
    Ok((basis, author))
}
// Interpret one already-selected event. Scheduling state stays in the caller.
fn interpret_event(
    facts: &[Fact],
    event: &Fact,
    operations: &[(EventId, Vec<Node>)],
    mut result: Tree,
) -> Result<(Tree, Vec<Node>), Error> {
    let (basis, mut author) = author_context(facts, event, operations)?;
    let mut seen = visible(&basis)?;
    let mut ops = Vec::new();
    if !event.insert.is_empty() {
        let gap = event.gap.ok_or(Error::Internal)?;
        for index in 0..event.insert.len() {
            let id = BirthId {
                event: event.id,
                index,
            };
            let op = author.insert(id, event.insert[index], &seen, add(gap, index)?)?;
            push(&mut ops, op)?;
            push(&mut seen, id)?;
        }
    }
    for i in 0..ops.len() {
        result.add(ops[i].clone())?;
    }
    Ok((result, ops))
}

// Retain the actual done vector as a private scheduling witness; no extra trace
// is allocated. The ordinary interpreter below erases it at the return boundary.
fn interpret_scheduled(facts: &[Fact]) -> Result<(Tree, Vec<EventId>), Error> {
    crate::event_shell::scheduled(
        facts,
        Tree::default(),
        &(),
        fact_id,
        scheduled_choose,
        scheduled_apply,
        internal_error,
    )
}
fn interpret(facts: &[Fact]) -> Result<Tree, Error> {
    let pair = interpret_scheduled(facts)?;
    let (tree, _) = pair;
    Ok(tree)
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Replica {
    writer: Option<Writer>,
    next_counter: u64,
    facts: Vec<Fact>,
    tree: Tree,
}
impl Replica {
    pub fn new(writer: Option<Writer>) -> Result<Self, Error> {

        Ok(Self {
            writer,
            next_counter: 1,
            facts: Vec::new(),
            tree: Tree::default(),
        })
    }
    pub fn facts(&self) -> &[Fact] {
        &self.facts
    }
    pub fn next_counter(&self) -> u64 {
        self.next_counter
    }
    pub fn whole(&self) -> Result<Vec<BirthId>, Error> {
        self.tree.whole()
    }
    pub fn observe(&self) -> Result<Vec<(BirthId, u32)>, Error> {
        let seen = visible(&self.facts)?;
        let mut out = Vec::new();
        let all = self.tree.whole()?;
        for id in all.iter() {
            if has_birth(&seen, *id) {
                push(&mut out, (*id, self.tree.node(*id)?.scalar))?;
            }
        }
        Ok(out)
    }
    fn duplicate(facts: &[Fact], fact: &Fact) -> Result<bool, Error> {
        if fact.id.counter == 0 || fact.id.counter > MAX_COUNTER {
            return Err(invalid(Invalid::Counter));
        }
        match crate::event_layer::classify(facts, fact, &TEXT_OPS.0) {
            None => Ok(false),
            Some(true) => Ok(true),
            Some(false) => Err(invalid(Invalid::Conflict)),
        }
    }
    fn validate_new(facts: &[Fact], fact: &Fact) -> Result<(), Error> {
        // Fact-local checks first: a fact that can never be valid must not be
        // reported as Missing (a deferral the caller retries) while its
        // dependencies are absent.
        validate_scalars(&fact.insert)?;
        if duplicate_births(&fact.delete) {
            return Err(invalid(Invalid::DeleteDuplicate));
        }
        if fact.insert.is_empty() && fact.gap.is_some() {
            return Err(invalid(Invalid::PlacementWithoutBirth));
        }
        if !fact.insert.is_empty() && fact.gap.is_none() {
            return Err(invalid(Invalid::Gap));
        }
        let selected = crate::event_layer::validate_event(facts, fact, &TEXT_OPS)?;
        let mut basis = Vec::new();
        for f in facts.iter() {
            if has_event(&selected, f.id) {
                push(&mut basis, f.clone())?;
            }
        }
        let seen = visible(&basis)?;
        for id in fact.delete.iter() {
            if !has_birth(&seen, *id) {
                return Err(invalid(Invalid::DeleteNotVisible));
            }
        }
        if !fact.insert.is_empty() && !matches!(fact.gap,Some(gap) if gap<=seen.len()) {
            return Err(invalid(Invalid::Gap));
        }
        Ok(())
    }
    // Final tree installation cannot replace the accepted fact set.
    fn with_tree(mut self, tree: Tree) -> Self {
        self.tree = tree;
        self
    }
    // Commit the calculated counter only after a successful plan.
    fn with_counter(mut self, counter: u64) -> Self {
        self.next_counter = counter;
        self
    }
    fn plan(&self, fact: &Fact) -> Result<Option<Self>, Error> {
        crate::event_shell::plan(
            self,
            fact,
            &(),
            plan_duplicate,
            plan_validate,
            plan_prepare,
            plan_execute,
        )
    }
    /// Consumes and returns the complete instance even on error. The borrowed
    /// input remains the caller's responsibility until Added/Duplicate succeeds.
    pub fn receive(self, fact: &Fact) -> (Self, Result<Admission, Error>) {
        crate::event_shell::receive(
            self,
            fact,
            &(),
            receive_plan,
            Admission::Added,
            Admission::Duplicate,
        )
    }
    /// One call is one primary edit. Gap is in the pre-edit author's view,
    /// including when this same fact deletes its predecessor or successor.
    pub fn edit(
        self,
        gap: usize,
        insert: Vec<u32>,
        delete: Vec<BirthId>,
    ) -> (Self, Result<Local, Error>) {
        let writer = match self.writer {
            Some(w) => w,
            None => return (self, Err(invalid(Invalid::NoWriter))),
        };
        if insert.is_empty() && delete.is_empty() {
            return (self, Ok(Local::Empty));
        }
        let next_counter = match next_counter_after(self.next_counter) {
            Ok(counter) => counter,
            Err(error) => return (self, Err(error)),
        };
        let after = match frontier(&self.facts) {
            Ok(ids) => ids,
            Err(error) => return (self, Err(error)),
        };
        let fact = Fact {
            id: EventId {
                writer,
                counter: self.next_counter,
            },
            after,
            gap: if insert.is_empty() { None } else { Some(gap) },
            insert,
            delete,
        };
        match self.plan(&fact) {
            Err(error) => (self, Err(error)),
            Ok(None) => (self, Err(invalid(Invalid::Conflict))),
            Ok(Some(mut next)) => {
                next = next.with_counter(next_counter);
                (next, Ok(Local::Authored(fact)))
            }
        }
    }
}

#[cfg(test)]
#[path = "edit/causal_basis_tests.rs"]
mod causal_basis_tests;

#[cfg(test)]
#[path = "edit/basis_filter_tests.rs"]
mod basis_filter_tests;

#[cfg(test)]
#[path = "edit/author_replay_tests.rs"]
mod author_replay_tests;

#[cfg(test)]
#[path = "edit/operation_provenance_tests.rs"]
mod operation_provenance_tests;

// Concrete projections connect the text fact to the arbitrary-event layer.
fn fact_id(fact: &Fact) -> EventId {
    fact.id
}
fn fact_after(fact: &Fact) -> &[EventId] {
    &fact.after
}
fn same_event_id(a: &EventId, b: &EventId) -> bool {
    *a == *b
}
fn earlier_event_id(a: &EventId, b: &EventId) -> bool {
    event_lt(*a, *b)
}
fn internal_error() -> Error {
    Error::Internal
}
fn missing_error() -> Error {
    Error::Missing
}
fn scheduled_choose(_: &(), facts: &[Fact], done: &[EventId]) -> Option<usize> {
    choose_ready(facts, done)
}
fn scheduled_apply(
    _: &(),
    facts: &[Fact],
    event: &Fact,
    operations: &[(EventId, Vec<Node>)],
    result: Tree,
) -> Result<(Tree, Vec<Node>), Error> {
    interpret_event(facts, event, operations, result)
}
fn plan_duplicate(_: &(), before: &Replica, fact: &Fact) -> Result<bool, Error> {
    Replica::duplicate(&before.facts, fact)
}
fn plan_validate(_: &(), before: &Replica, fact: &Fact) -> Result<(), Error> {
    Replica::validate_new(&before.facts, fact)
}
fn plan_prepare(_: &(), mut next: Replica, fact: &Fact) -> Result<Replica, Error> {
    push(&mut next.facts, fact.clone())?;
    next.facts = canonical(&next.facts)?;
    Ok(next)
}
fn plan_execute(_: &(), next: Replica) -> Result<Replica, Error> {
    let tree = interpret(&next.facts)?;

    Ok(next.with_tree(tree))
}
fn receive_plan(_: &(), before: &Replica, fact: &Fact) -> Result<Option<Replica>, Error> {
    before.plan(fact)
}

fn required_predecessor(id: &EventId) -> Option<EventId> {
    if id.counter > 1 {
        Some(EventId {
            writer: id.writer,
            counter: id.counter - 1,
        })
    } else {
        None
    }
}
fn forbidden_ancestor(ancestor: &EventId, current: &EventId) -> bool {
    ancestor.writer == current.writer && ancestor.counter >= current.counter
}


fn duplicate_dependency_error() -> Error {
    invalid(Invalid::DependencyDuplicate)
}
fn predecessor_error() -> Error {
    invalid(Invalid::Predecessor)
}

// One text policy; construction-site controls bind both comparison positions.
const TEXT_OPS: crate::event_layer::EventOps<Fact, EventId, Error> = {
    crate::event_layer::event_ops(
        crate::event_layer::graph_ops(
            fact_id, fact_after, same_event_id, earlier_event_id,
            clone_selected_fact, fact_equal, internal_error, missing_error,
        ),
        required_predecessor, forbidden_ancestor, duplicate_dependency_error, predecessor_error,
    )
};
