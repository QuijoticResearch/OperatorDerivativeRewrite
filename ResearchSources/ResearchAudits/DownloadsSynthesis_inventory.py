from pathlib import Path
import re, hashlib, json, collections
root=Path(r'C:\Users\ramir\Downloads')
out=Path(r'C:\Operator\ResearchAudits\DownloadsSynthesis')
out.mkdir(exist_ok=True)
def arg(s, start):
    i=s.find('{',start)
    if i<0:return ''
    depth=1;j=i+1
    while j<len(s) and depth:
        if s[j]=='{' and s[j-1]!='\\':depth+=1
        elif s[j]=='}' and s[j-1]!='\\':depth-=1
        j+=1
    return re.sub(r'\s+',' ',s[i+1:j-1]).strip()
rows=[]; claims=[]; seen={}
for p in sorted(root.rglob('*.tex')):
    raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest();s=raw.decode('utf-8-sig',errors='replace')
    titles=[]
    for m in re.finditer(r'\\(?:title|papertitle)(?:\[[^\]]*\])?\s*\{',s):
        titles.append(arg(s,m.start()))
    envs=set(['theorem','lemma','proposition','corollary','definition','conjecture','thm','lem','prop','cor','defn','assumption','hypothesis','remark'])
    envs.update(re.findall(r'\\newtheorem\*?\{([^}]+)\}',s))
    count=collections.Counter()
    local=[]
    for m in re.finditer(r'\\begin\{([^}]+)\}(?:\[([^\]]*)\])?',s):
        env=m.group(1)
        if env not in envs:continue
        end=s.find('\\end{'+env+'}',m.end())
        if end<0:continue
        count[env]+=1
        if h in seen:continue
        body=s[m.end():end].strip()
        labels=re.findall(r'\\label\{([^}]+)\}',body)
        tail=s[end+len('\\end{'+env+'}'):]
        proof=''
        pm=re.match(r'\s*(?:%[^\n]*\n\s*)*\\begin\{proof\}(?:\[[^\]]*\])?',tail)
        if pm:
            pe=tail.find('\\end{proof}',pm.end())
            if pe>=0:proof=tail[pm.end():pe].strip()
        local.append(dict(path=str(p),sha256=h,line=s.count('\n',0,m.start())+1,environment=env,name=m.group(2) or '',labels=labels,statement=body,following_proof=proof,status='UNVERIFIED'))
    rows.append(dict(path=str(p),sha256=h,bytes=len(raw),title=titles[0] if titles else '',declaration_counts=dict(count),duplicate_of=seen.get(h),modified=p.stat().st_mtime))
    if h not in seen:seen[h]=str(p);claims.extend(local)
(out/'manifest.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2),encoding='utf8')
(out/'claims.json').write_text(json.dumps(claims,ensure_ascii=False,indent=2),encoding='utf8')
lines=['# Downloads LaTeX inventory','', 'All extracted claims are UNVERIFIED. This is a source index, not validation. Exact-byte duplicates are grouped by SHA-256. Different versions remain separate.','',f'{len(rows)} files; {len(seen)} unique byte contents; {len(claims)} extracted environments from unique sources.','', '| Source | Title | Environments | Exact duplicate |','|---|---|---:|---|']
for r in rows:
    esc=lambda x:x.replace('|','\\|').replace('\n',' ')
    lines.append(f"| {esc(r['path'])} | {esc(r['title'])} | {sum(r['declaration_counts'].values())} | {esc(r['duplicate_of'] or '')} |")
(out/'SOURCE_INVENTORY.md').write_text('\n'.join(lines)+'\n',encoding='utf8')
print(json.dumps(dict(files=len(rows),unique=len(seen),duplicates=len(rows)-len(seen),extracted_environments=len(claims),total_bytes=sum(r['bytes'] for r in rows))))
for r in rows:
    if not r['duplicate_of'] and re.search(r'iterated_gamma|ibm|bidegree|first.?chaos|volterra|fractional_memory|banach|operator.deriv|sobolev|energy.first',r['path'],re.I):
        print(Path(r['path']).name+' | '+r['title'][:180])
