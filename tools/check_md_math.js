// GitHub renders md math with KaTeX, so render every expression here and fail on any error.
//   cd md/YAPSS && npm install katex && node ../../tools/check_md_math.js
// Two failure modes this catches, both of which break GitHub rendering:
//   * inline math $...$ spanning a line break (GitHub does not allow it, and the stray $
//     then swallows a later $$ block, producing "Missing \\end{aligned}");
//   * a $ nested inside \\text{...}, which terminates the surrounding math early.
const katex=require('katex');
const fs=require('fs');
let total=0, bad=0;
const files=fs.readdirSync('.').filter(f=>f.endsWith('.md')).sort();
for(const f of files){
  let src=fs.readFileSync(f,'utf8');
  // strip fenced code
  src=src.replace(/```[\s\S]*?```/g,m=>m.replace(/[^\n]/g,' '));
  const errs=[];
  const lineOf=(idx)=>src.slice(0,idx).split('\n').length;
  // display math
  let masked=src;
  const dre=/\$\$([\s\S]*?)\$\$/g; let m;
  while((m=dre.exec(src))!==null){
    total++;
    try{ katex.renderToString(m[1],{displayMode:true,throwOnError:true,strict:false}); }
    catch(e){ bad++; errs.push([lineOf(m.index),'display',e.message.slice(0,90)]); }
    masked=masked.slice(0,m.index)+' '.repeat(m[0].length)+masked.slice(m.index+m[0].length);
  }
  // inline math (single line)
  const ire=/\$([^$\n]+)\$/g;
  while((m=ire.exec(masked))!==null){
    total++;
    try{ katex.renderToString(m[1],{displayMode:false,throwOnError:true,strict:false}); }
    catch(e){ bad++; errs.push([lineOf(m.index),'inline',e.message.slice(0,90)]); }
  }
  if(errs.length){
    console.log(`\n=== ${f}: ${errs.length} errors ===`);
    for(const e of errs.slice(0,6)) console.log(`  L${e[0]} ${e[1]}: ${e[2]}`);
  }
}
console.log(`\nTOTAL math expressions: ${total}, errors: ${bad}`);
process.exit(bad?1:0);
