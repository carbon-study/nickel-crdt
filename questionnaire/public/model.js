import { questions, revision, title } from './questions.js';
export const format = 'nickel-undo-answers-v1';
export const storageKey = 'nickel-undo-questionnaire:'+revision;
export const assumptions = [
  'Each question is independent. Quoted letters are text; Alice and Bo are writers.',
  'Each listed edit is its own item unless explicit grouping or child membership is stated.',
  'Concurrent means neither writer saw the other operation when issuing its own.',
  'Some questions stipulate an observed intermediate result; that is not an endorsement of your earlier answer.',
  'There is no answer key, score, adopted Nickel policy or CRDT simulation behind this questionnaire.'
];
export const emptyState = () => ({respondent:'',answers:{},current:0});
const text = (x,max) => { if(typeof x!=='string'||x.length>max)throw Error('invalid or oversized text');return x; };
export function normalizeState(raw) {
  if(!raw || typeof raw!=='object'||Array.isArray(raw)||!raw.answers||typeof raw.answers!=='object'||Array.isArray(raw.answers))throw Error('invalid saved answers');
  const state=emptyState();state.respondent=text(raw.respondent??'',200);
  if(!Number.isInteger(raw.current)||raw.current<0||raw.current>=questions.length)throw Error('invalid question position');state.current=raw.current;
  for(const [id,a] of Object.entries(raw.answers)) {
    const q=questions.find(q=>q.id===id);if(!q||!a||typeof a!=='object')throw Error('unknown answer');
    if(a.choice!==null&&!q.choices.some(c=>c.id===a.choice))throw Error('unknown choice');
    state.answers[id]={choice:a.choice,note:text(a.note,10000)};
  }
  return state;
}
export function answered(q,a) {return !!a&&(q.free?a.note.trim().length>0:q.choices.some(c=>c.id===a.choice));}
export const countAnswered = state => questions.filter(q=>answered(q,state.answers[q.id])).length;
export function exportAnswers(state,at=new Date().toISOString()) {
  const s=normalizeState(state);
  return {format,questionnaireVersion:revision,title,assumptions,exportedAt:at,respondent:s.respondent.trim(),answeredCount:countAnswered(s),totalQuestions:questions.length,
    answers:questions.map(q=>{const a=s.answers[q.id];return {question:q,status:answered(q,a)?'answered':a?.note?'draft':'unanswered',
      answer:a?{choiceId:a.choice,choiceLabel:q.choices.find(c=>c.id===a.choice)?.label??null,note:a.note}:null};})};
}
export function importAnswers(raw) {
  if(raw?.format!==format||raw.questionnaireVersion!==revision||!Array.isArray(raw.answers)||raw.answers.length!==questions.length)throw Error('This is not an export from this questionnaire version.');
  const state=emptyState();state.respondent=text(raw.respondent??'',200);const seen=new Set();
  for(const row of raw.answers){const q=questions.find(q=>q.id===row?.question?.id);if(!q||seen.has(q.id)||JSON.stringify(row.question)!==JSON.stringify(q))throw Error('Question content does not match this version.');seen.add(q.id);
    if(row.answer!==null){if(!row.answer||typeof row.answer!=='object')throw Error('invalid answer');state.answers[q.id]={choice:row.answer.choiceId,note:row.answer.note};}
  }
  return normalizeState(state);
}
