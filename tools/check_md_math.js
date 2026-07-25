// GitHub renders md math with KaTeX.  Display math must be written as a ```math fence:
// inside $$...$$ GitHub's Markdown escaping first turns \\ into \ (and \{ into {, ...),
// which breaks \begin{aligned} rows and makes KaTeX report "Missing \end{aligned}".
// A code fence is not touched by Markdown escaping, so it renders exactly as written.
// Inline math stays $...$ and must not span a line break, nor contain $ inside \text{}.
//   cd md/YAPSS && NODE_PATH=<dir with katex> node ../../tools/check_md_math.js
const katex=require('katex');
const fs=require('fs');
let total=0,bad=0;
for(const f of fs.readdirSync('.').filter(x=>x.endsWith('.md')).sort()){
  const src=fs.readFileSync(f,'utf8'); const lines=src.split('\n');
  const errs=[]; let i=0;
  let masked=[];
  while(i<lines.length){
    const s=lines[i].trim();
    if(s.startsWith('```')){
      const isMath = s==='```math';
      let j=i+1; const body=[];
      while(j<lines.length && lines[j].trim()!=='```'){ body.push(lines[j]); j++; }
      if(isMath){ total++;
        try{ katex.renderToString(body.join('\n'),{displayMode:true,throwOnError:true,strict:false}); }
        catch(e){ bad++; errs.push([i+1,'math-fence',e.message.slice(0,80)]); }
      }
      for(let k=i;k<=j;k++) masked.push('');
      i=j+1; continue;
    }
    masked.push(lines[i]); i++;
  }
  const ire=/\$([^$\n]+)\$/g; let m; const joined=masked.join('\n');
  while((m=ire.exec(joined))!==null){ total++;
    try{ katex.renderToString(m[1],{displayMode:false,throwOnError:true,strict:false}); }
    catch(e){ bad++; errs.push([joined.slice(0,m.index).split('\n').length,'inline',e.message.slice(0,80)]); }
  }
  if(errs.length){ console.log(`\n=== ${f}: ${errs.length} ===`); errs.slice(0,5).forEach(e=>console.log(`  L${e[0]} ${e[1]}: ${e[2]}`)); }
}
console.log(`\nTOTAL: ${total}, errors: ${bad}`);
process.exit(bad?1:0);
