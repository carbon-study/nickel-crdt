import fs from 'node:fs';
import {questions,revision} from '../public/questions.js';
import {emptyState,exportAnswers,importAnswers,countAnswered} from '../public/model.js';
const state=emptyState();
for(const q of questions)state.answers[q.id]={choice:null,note:''};
const template=exportAnswers(state,'2026-11-01T00:00:00.000Z');
const md=[`# undo decisions — ${revision}`, '', 'The same 40 questions as the web edition, without a browser.', '', 'Fill in undo-answers-template.json: set respondent, then each answer.choiceId to the quoted choice ID and answer.note to your explanation. Leave choiceId null when unanswered; q40 uses only note. Do not edit question snapshots. choiceLabel and status are derived metadata: the browser regenerates them on export. Import the completed file into the web quiz to review it or export a normalized copy. Partial answers are welcome.', '', ...template.assumptions.map(x=>`- ${x}`),''];
for(const q of questions){md.push(`## ${q.id}: ${q.title}`, '', q.section, '', ...q.events.map((s,i)=>`${i+1}. ${s}`),'',q.prompt,'',...q.choices.map(c=>`- \`${c.id}\`: ${c.label}`),'');}
const files={'undo-questions.md':md.join('\n')+'\n','undo-answers-template.json':JSON.stringify(template,null,2)+'\n'};
for(const [name,body] of Object.entries(files)){
 const path=new URL('../public/'+name,import.meta.url);
 if(process.argv.includes('--check')){if(fs.readFileSync(path,'utf8')!==body)throw Error('stale portable file: '+name);}else fs.writeFileSync(path,body);
}
const round=importAnswers(template);if(countAnswered(round)!==0)throw Error('blank template answered');
for(const q of questions)round.answers[q.id]={choice:q.free?null:q.choices[0].id,note:'portable reply'};
if(countAnswered(importAnswers(exportAnswers(round)))!==40)throw Error('filled roundtrip failed');
console.log('portable files and blank/full import roundtrips checked');
