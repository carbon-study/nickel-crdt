import assert from 'node:assert/strict';
import {questions,revision} from '../public/questions.js';
import {emptyState,normalizeState,exportAnswers,importAnswers,countAnswered} from '../public/model.js';
assert.equal(questions.length,40);assert(questions.length<=100);assert.equal(new Set(questions.map(q=>q.id)).size,questions.length);
for(const q of questions){assert(q.title&&q.prompt);assert(Array.isArray(q.events));assert.equal(new Set(q.choices.map(c=>c.id)).size,q.choices.length);if(!q.free){assert(q.choices.some(c=>c.id==='other'));assert(q.choices.some(c=>c.id==='unsure'));}}
const s=emptyState();s.respondent='test';s.current=4;s.answers.q01={choice:'unsure',note:'it depends <script>alert(1)</script>'};s.answers.q02={choice:null,note:'draft only'};s.answers.q40={choice:null,note:'keep identities'};assert.equal(countAnswered(s),2);
const x=exportAnswers(s,'2026-11-01T00:00:00Z');assert.equal(x.questionnaireVersion,revision);assert.equal(x.answers.length,40);assert.equal(x.answeredCount,2);assert.equal(x.answers[1].status,'draft');assert.equal(x.answers[2].answer,null);assert.deepEqual(x.answers[0].question,questions[0]);assert.equal(x.answers[0].answer.choiceLabel,'depends / unsure — explain if you can');
const back=importAnswers(JSON.parse(JSON.stringify(x)));assert.deepEqual(back.answers,s.answers);assert.equal(back.respondent,s.respondent);assert.equal(back.current,0);
for(const mutate of [y=>y.questionnaireVersion='bad',y=>y.answers.pop(),y=>y.answers[1]=y.answers[0],y=>y.answers[0].question.title='changed',y=>y.answers[0].answer.choiceId='unknown',y=>y.answers[0].answer.note='a'.repeat(10001)]){const y=structuredClone(x);mutate(y);assert.throws(()=>importAnswers(y));}
assert.throws(()=>normalizeState({...s,current:40}));assert.throws(()=>normalizeState({...s,answers:{bad:{choice:null,note:''}}}));assert.equal(countAnswered(emptyState()),0);assert.equal(exportAnswers(emptyState()).answers.filter(a=>a.status==='unanswered').length,40);
console.log('PASS 40-question integrity; partial/full export; roundtrip; invalid imports reject');
