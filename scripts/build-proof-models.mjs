import {mkdir,copyFile,writeFile,readFile} from 'node:fs/promises';
import {join,basename} from 'node:path';
import {verify,modelIncludes} from './proof-cache.mjs';
import {checkTimeoutBudgets} from './check-proof-timeouts.mjs';
const {NICKEL_PROOF_FSTAR:fstar,NICKEL_HAX_SOURCE:models}=process.env;
const output=process.argv[2];if(!fstar||!models||!output)throw Error('supply F* pin, hax source and output directory');
await checkTimeoutBudgets();
const dir=join(process.cwd(),'model-work');await mkdir(dir,{recursive:true});
const names=['Core_models.Convert.fst','Core_models.fst','Alloc.Slice.fst','Rust_primitives.Hax.Folds.fsti','Core_models.Iter.Adapters.Filter.fst','Core_models.Iter.Adapters.Rev.fst','Core_models.Iter.Adapters.Map.fst','Rust_primitives.Hax.Monomorphized_update_at.fsti'];
const roots=[];
for(const name of names){let found;for(const base of modelIncludes(models)){try {await readFile(join(base,name));found=join(base,name);break;}catch(e){if(e.code!=='ENOENT')throw e;}}if(!found)throw Error('missing model '+name);roots.push(found);}
// Cold imported models get a separate bounded allowance. Project callers
// retain the default 60s; the solver settings and all proof goals are unchanged.
const result=await verify({dir,roots,fstar,models,moduleSeconds:180,seconds:600});
if(result.status!==0)throw Error(result.log);
await mkdir(output,{recursive:true});
await writeFile(join(output,'bootstrap.log'),result.log);
const moduleTimings=[...result.log.matchAll(/^TOTAL TIME (\d+) ms:.*\s(\S+\.fsti?)\s*$/gm)].map(m=>({module:basename(m[2]),milliseconds:Number(m[1])}));
await writeFile(join(output,'bootstrap.stats.json'),JSON.stringify({moduleSeconds:180,makeSeconds:600,dependencySeconds:60,rlimit:100,status:result.status,moduleTimings,declarations:result.stats},null,2)+'\n');
const {readdir}=await import('node:fs/promises');
for(const file of await readdir(join(dir,'checked')))if(file.endsWith('.checked'))await copyFile(join(dir,'checked',file),join(output,file));
await writeFile(join(output,'identity.json'),JSON.stringify({fstar,models,roots},null,2)+'\n');
