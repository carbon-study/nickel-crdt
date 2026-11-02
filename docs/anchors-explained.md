# anchors, cursors and storage, explained with pictures

**Status: explanation only.** The [response plan](response-plan.md) asks for
worked examples for the anchor questions before any identity or restoration law
is adopted. Ren answered q33, q34 and q37 "unsure", noting that he didn't
understand the question. That records an explanation failure, not a rejection. This document
explains q30–q34 and q37, plus the q39 boundary Ren has already settled. It
doesn't pick a policy. Where it says "the library could…", read "this is one
of the options".

Notation: `|` is a cursor or gap, `[` `]` mark a highlight, and a struck-out
letter like ~~a~~ is deleted but still remembered.

## 1. what an anchor is

Suppose a comment points at the word "cat".

```text
the cat sat         comment → "cat"   (characters 4–7)
```

Someone types "big " before it:

```text
the big cat sat     comment → ???
```

If the comment remembered *"characters 4–7"*, it would now point at "big ".
An **anchor** remembers *which characters* instead: "the c-a-t that Alice
typed". Text can be inserted before it, after it or around it, and the anchor
still finds "cat".

Carbon needs anchors for anything that points into text:

- a highlight's start and end
- a note attached to a sentence
- a cursor or selection
- a comment

In the contract, `anchor(…)` makes one and `resolve(…)` turns it back into a
current position.

## 2. two different questions at a boundary

An anchor sits *between* two characters. When someone types exactly there, two
separate questions come up. They're easy to blur together.

### 2a. which side does the anchor stay on? (affinity)

```text
before:   ab|c          an anchor between b and c
type X at the anchor:
  left affinity:    abX|c   anchor stays glued to b, so X lands before it
  right affinity:   ab|Xc   anchor stays glued to c, so X lands after it
```

Affinity is just "which neighbour am I attached to". A cursor usually wants
left affinity, so that typed text appears before it and the cursor moves along.
The end of a highlight might want either.

### 2b. does the new text belong to the span? (membership)

```text
a link:   see [docs] now
type X right after "docs":
  joins the link:      see [docsX] now
  stays outside:       see [docs]X now
```

Both results put X at the *same visible position*. The only difference is
whether X is part of the link.

A range's endpoints have their own affinity, and the
[contract](carbon-contract.md) uses it for exactly this: the end's affinity
decides whether typing at that edge enlarges the range. But that is **one fixed
rule per range**, the same for every keystroke. A cursor's affinity answers a
different question: does the cursor move along with what you type? Neither one
says "*this* keystroke belongs inside". "Inside the link" isn't the same thing
as "attached to the left character".

### Ren's Obsidian cursor (q32)

In Obsidian, when the cursor sits at the end of a link and you press →, the
cursor doesn't visibly move. It steps from *inside* the link to *outside* it,
and what you type next follows that choice.

```text
see [docs|] now     cursor inside: typing extends the link
        press →
see [docs]| now     cursor outside: typing is plain text
```

This uses both layers:

- the cursor is an anchor with an affinity (which side it sticks to), **and**
- the editor tracks whether the cursor is inside or outside the span
  (membership).

The **editor** decides how arrow keys move between those states. What Nickel
has to provide is a way to *carry out* the choice: when text is typed at the
link's edge, put it inside or outside the link for this insertion, even though
the link's own edge rule says otherwise. Fixed edge affinity alone can't do
that. Whether the API gets such a per-insertion choice, or leaves the editor to
adjust the range afterwards, is what q32 is really asking.

## 3. anchors through deleted text (q30, q31)

Nickel remembers deleted characters (so that undo can bring them back). That
lets an anchor, or a gap you insert into, remember *where it was relative to
hidden text*.

```text
start:    a b                   visible "ab"
gap before a:     |a b
delete a:         |~~a~~ b      visible "b"
insert X there:   X ~~a~~ b     visible "Xb"
undo the delete:  X a b         visible "Xab"   ← q30
```

```text
start:    a b
gap after a:      a| b
delete a:         ~~a~~| b      visible "b"  (looks exactly like the case above!)
insert X there:   ~~a~~ X b     visible "Xb"
undo the delete:  a X b         visible "aXb"   ← q31
```

Both histories show the same text, "Xb", in the middle. They only differ
*after* the undo. q30 and q31 ask whether the library should remember that
difference (so the results differ: "Xab" vs "aXb"), or treat both gaps the same
once `a` is hidden (option 3 in each question).

Remembering it is what the API draft's `Gap` and `Anchor` types promise
("retain historical identity/order and affinity", in
[api-verification.md](api-verification.md)). Not remembering it is simpler, but
then a restored character can land on the "wrong" side of text typed while it
was gone.

**This needs a decision.** Ren answered "Xab" for *both* q30 and q31. Witness 7
("historical side") in [carbon-contract.md](carbon-contract.md) currently
requires "Xab" for the first history and "aXb" for the second. One of them has
to change. If "Xab" both times is the intended rule, then X always lands before
a restored neighbour, whichever side of it X was typed on. That gives up the
historical side, and witness 7 and the `Gap` promise would need rewording. If
the q31 answer came from an unclear question, the pictures above are meant to
fix that.

The same "where was it?" question comes up in the UI. To mark deleted text
inline before offering Restore, an editor resolves an anchor on the hidden
text to a visible position. The contract says hidden anchors stay valid while
history is retained. Which side of other hidden or newly typed text the marker
lands on is the same question as q30/q31, and the complete ordering
specification for it (obligation V6) is still missing.

## 4. cursors after undo and redo (q33)

```text
1. you make an edit with two cursors, then move both cursors somewhere else
2. undo        (the edit disappears)
3. you move the cursors again
4. redo        (the edit comes back)  → where should the cursors go?
```

The options are:

- where they were when the edit finished,
- where they were when you pressed undo,
- where they were just before redo,
- or nowhere special: leave them where they are and let the redone text push
  them along.

This is **editor policy**: Nickel doesn't own your cursors. What Nickel must
provide is anchors that still resolve correctly after undo and redo, so the
editor *can* implement whichever choice it prefers.

## 5. is redone text the same text? (q34)

```text
Alice types "a".  Bo puts a comment anchor on it.
Alice undoes, then redoes.  The screen shows "a" again.
Is Bo's comment still attached?
```

- **Same element:** the redone "a" *is* the original character, switched back
  on. Bo's anchor just works.
- **Fresh element:** redo inserts a new "a" that happens to look the same. Bo's
  anchor points at the old, now-dead character, and needs a documented
  fallback (for example, "move to the nearest live neighbour").

The merged Python reference model
([private-session profile](private-session-profile.md); not the engine) gives
"same element" in both ways the "a" can come back: redo switches Alice's original element back
on, and so does an explicit Restore. Neither creates a fresh "a", so Bo's
anchor keeps working. q34 asks whether nickel should *promise* that, or
whether it's just what this model happens to do.

## 6. when history gets too big (q37)

Nickel keeps deleted characters and old operations so that anchors (section 3)
and undo can use them. On a phone, that history eventually takes up space.

```text
the document you see:    "the cat sat"              tiny
what Nickel remembers:   every character ever typed, every deletion,
                         every undo/redo switch     grows forever
```

Some of that history might still matter to a device that's been offline for a
month. The question is what to do when a configured limit is hit:

1. refuse to grow further and offer export, never silently changing meaning
2. drop *this device's* undo ability, but keep everything other devices need
3. delete old history only after a protocol proves no device still needs it
4. start a fresh document and make every device switch to it

For a first release, the choice is about safety versus convenience. None of
these options changes what you see today. They change what still works next
month.

## 7. two kinds of history (q39, settled)

Ren clarified q39: **your undo/redo history stays on your device.** A new
device opening the document doesn't inherit your undo stack.

That is a different thing from the **shared facts** every copy of the document
needs in order to merge future edits correctly:

| | private undo history | shared document facts |
| --- | --- | --- |
| what | "my last 20 actions, in order" | which characters exist, their order, what's deleted, which deletions were reversed |
| who has it | your device only | every copy, including fresh ones |
| why | so *your* undo button works | so everyone converges, and anchors and later undos mean the same thing everywhere |

Ren's own test model showed why the second column has to include "which
deletions were reversed". Two histories can look identical on screen but still
need to behave differently on the next undo.
