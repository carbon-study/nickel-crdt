import {mkdir,copyFile,writeFile,readFile} from 'node:fs/promises';
import {join} from 'node:path';
import {verify,modelIncludes} from './proof-cache.mjs';
const {NICKEL_PROOF_FSTAR:fstar,NICKEL_HAX_SOURCE:models}=process.env;
const output=process.argv[2];if(!fstar||!models||!output)throw Error('supply F* pin, hax source and output directory');
const dir=join(process.cwd(),'model-work');await mkdir(dir,{recursive:true});
const names=['Core_models.Convert.fst','Core_models.fst','Alloc.Slice.fst','Rust_primitives.Hax.Folds.fsti'];
const roots=[];
for(const name of names){let found;for(const base of modelIncludes(models)){try {await readFile(join(base,name));found=join(base,name);break;}catch(e){if(e.code!=='ENOENT')throw e;}}if(!found)throw Error('missing model '+name);roots.push(found);}
// One-time cold library bootstrap; each individual F* process still has 60s.
const result=await verify({dir,roots,fstar,models,seconds:180});
if(result.status!==0)throw Error(result.log);
await mkdir(output,{recursive:true});
const {readdir}=await import('node:fs/promises');
for(const file of await readdir(join(dir,'checked')))if(file.endsWith('.checked'))await copyFile(join(dir,'checked',file),join(output,file));
await writeFile(join(output,'identity.json'),JSON.stringify({fstar,models,roots},null,2)+'\n');
