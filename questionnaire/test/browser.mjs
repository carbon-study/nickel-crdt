import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {pathToFileURL} from 'node:url';
const {chromium}=await import(pathToFileURL(process.env.QUIZ_BROWSER_MODULE).href);
const base=process.argv[2]??'http://127.0.0.1:4186';
const browser=await chromium.launch({headless:true});
let checks=0;
const download=async page=>{const wait=page.waitForEvent('download');await page.locator('#export').click();const d=await wait,p=await d.path();return {data:JSON.parse(await fs.readFile(p,'utf8')),path:p};};
try{
 const context=await browser.newContext({acceptDownloads:true}),page=await context.newPage(),errors=[];page.on('pageerror',e=>errors.push(e.message));
 await page.goto(base,{waitUntil:'networkidle'});await page.locator('#question-nav button').nth(39).waitFor();assert.equal(await page.locator('#question-nav button').count(),40);assert.match(await page.locator('#progress-label').innerText(),/^0 \/ 40/);
 let requests=[];page.on('request',r=>requests.push(r.url()));
 await page.locator('#respondent').fill('browser test');await page.locator('input[value="unsure"]').check();await page.locator('#note').fill('<img src=x onerror=alert(1)> depends');
 let partial=await download(page);assert.equal(partial.data.answeredCount,1);assert.equal(partial.data.answers.length,40);assert.equal(partial.data.answers[0].answer.choiceId,'unsure');assert(partial.data.answers[0].question.events.length);assert.equal(partial.data.answers[1].answer,null);
 assert.deepEqual(requests,[],'answering/exporting must issue no requests');
 await page.reload({waitUntil:'networkidle'});assert(await page.locator('input[value="unsure"]').isChecked());assert.equal(await page.locator('#note').inputValue(),'<img src=x onerror=alert(1)> depends');
 for(let i=0;i<40;i++){await page.locator('#question-nav button').nth(i).click();if(i===39)await page.locator('#note').fill('nothing to add');else await page.locator('input[name="answer"]').first().check();}
 assert.equal(await page.locator('#progress-label').innerText(),'40 / 40 answered');const full=await download(page);assert.equal(full.data.answeredCount,40);assert.equal(full.data.answers.filter(a=>a.status==='answered').length,40);
 await page.locator('#review-button').click();assert.equal(await page.locator('.review-item').count(),40);assert.equal(await page.locator('#review-list img').count(),0);assert((await page.locator('#review-list').innerText()).includes('<img src=x onerror=alert(1)> depends'));
 page.once('dialog',d=>d.accept());await page.locator('#clear').click();assert.equal(await page.locator('#progress-label').innerText(),'0 / 40 answered');
 await page.locator('#import').setInputFiles({name:'response.json',mimeType:'application/json',buffer:Buffer.from(JSON.stringify(full.data))});await page.waitForFunction(()=>document.querySelector('#progress-label').textContent==='40 / 40 answered');
 const bad=structuredClone(full.data);bad.answers[0].question.title='changed';await page.locator('#import').setInputFiles({name:'bad.json',mimeType:'application/json',buffer:Buffer.from(JSON.stringify(bad))});await page.waitForFunction(()=>document.querySelector('#storage-warning').textContent.startsWith('Import rejected'));assert.equal(await page.locator('#progress-label').innerText(),'40 / 40 answered');
 for(const width of [320,390,1280]){await page.setViewportSize({width,height:900});await page.locator('#back-to-question').isVisible().then(async v=>{if(v)await page.locator('#back-to-question').click();});assert(await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth),'no horizontal page overflow at '+width);if(width===390)await page.screenshot({path:'/tmp/nickel-quiz-mobile.png',fullPage:true});}
 const tab=await context.newPage();await tab.goto(base,{waitUntil:'networkidle'});await tab.locator('#question-nav button').nth(39).waitFor();await page.locator('#question-nav button').first().click();await page.locator('input[value="2"]').check();await tab.waitForFunction(()=>document.querySelector('#storage-warning').textContent.startsWith('Another tab'));await tab.locator('input[value="1"]').check();await page.reload({waitUntil:'networkidle'});assert(await page.locator('input[value="2"]').isChecked(),'stale tab must not overwrite newer saved response');
 assert.deepEqual(errors,[]);await context.close();checks++;
 const blocked=await browser.newContext({acceptDownloads:true});await blocked.addInitScript(()=>Object.defineProperty(window,'localStorage',{get(){throw Error('blocked for test');}}));const p=await blocked.newPage();await p.goto(base,{waitUntil:'networkidle'});await p.locator('input[name="answer"]').first().check();assert((await p.locator('#storage-warning').innerText()).includes('could not save'));assert.equal((await download(p)).data.answeredCount,1);await blocked.close();checks++;
 console.log('PASS browser: partial/full JSON download, local reload, import/rejection, safe text rendering, 320/390/1280 layout, cross-tab protection, storage-denied export; '+checks+' contexts');
}finally{await browser.close();}
