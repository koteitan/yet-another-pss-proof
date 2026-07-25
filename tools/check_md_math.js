// GitHub applies Markdown escaping INSIDE math, which silently corrupts formulas:
//   $$ ... \\ ... $$      ->  \\ becomes \   -> \begin{aligned} loses its row breaks
//                               -> GitHub reports "Missing \end{aligned}"
//   $ ... \{x\} ... $      ->  becomes {x}     -> the braces disappear
//   $ ... a \, b ... $      ->  becomes a , b   -> a stray comma is rendered
// Neither happens inside a code span or a code fence, so this repository writes
//   display math as a ```math fence, and inline math as $`...`$ .
// This script renders every formula with KaTeX and also fails on any unprotected $.
//   cd md/YAPSS && NODE_PATH=<dir containing katex> node ../../tools/check_md_math.js
const katex=require('katex');
const fs=require('fs');
let total=0,bad=0;
for(const f of fs.readdirSync('.').filter(x=>x.endsWith('.md')).sort()){
  const lines=fs.readFileSync(f,'utf8').split('\n'); const errs=[]; let i=0; const rest=[];
  while(i<lines.length){
    const s=lines[i].trim();
    if(s.startsWith('```')){
      const isMath=s==='```math'; let j=i+1; const body=[];
      while(j<lines.length && lines[j].trim()!=='```'){ body.push(lines[j]); j++; }
      if(isMath){ total++;
        try{ katex.renderToString(body.join('\n'),{displayMode:true,throwOnError:true,strict:false}); }
        catch(e){ bad++; errs.push([i+1,'fence',e.message.slice(0,70)]); } }
      for(let k=i;k<=j;k++) rest.push(''); i=j+1; continue; }
    rest.push(lines[i]); i++;
  }
  const joined=rest.join('\n');
  const re=/\$`([^`]+)`\$/g; let m;
  while((m=re.exec(joined))!==null){ total++;
    try{ katex.renderToString(m[1],{displayMode:false,throwOnError:true,strict:false}); }
    catch(e){ bad++; errs.push([joined.slice(0,m.index).split('\n').length,'inline',e.message.slice(0,70)]); } }
  const un=joined.replace(/\$`[^`]+`\$/g,'').match(/\$/g);
  if(un){ errs.push([0,'unprotected','stray $ x'+un.length]); bad+=un.length; }
  if(errs.length){ console.log(`\n=== ${f} ===`); errs.slice(0,4).forEach(e=>console.log(`  L${e[0]} ${e[1]}: ${e[2]}`)); }
}
console.log(`\nTOTAL: ${total}, errors: ${bad}`); process.exit(bad?1:0);
