#!/usr/bin/env python3
"""Audit faithful periodic native inputs without counting absent ISS effects."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time


WRAPPER = r'''#!/usr/bin/env python3
import hashlib,json,os,pathlib,subprocess,sys,time
root=pathlib.Path(os.environ['ISS_PERIODIC_LOG'])
directory=root/str(time.time_ns()); directory.mkdir(parents=True)
args=sys.argv[1:]; source=pathlib.Path(args[-1]); data=source.read_bytes()
(directory/'input.scop').write_bytes(data)
p=subprocess.run([os.environ['ISS_REAL_PLUTO'],*args],capture_output=True)
(directory/'stdout.txt').write_bytes(p.stdout);(directory/'stderr.txt').write_bytes(p.stderr)
for suffix in ['.beforescheduling.scop','.midtransform.scop','.posttile.scop','.afterscheduling.scop']:
    path=pathlib.Path(str(source)+suffix)
    if path.exists(): (directory/('output'+suffix)).write_bytes(path.read_bytes())
record={'command':[os.environ['ISS_REAL_PLUTO'],*args], 'returncode':p.returncode,
        'input_statements':data.count(b'\nDOMAIN\n'),'input_sha256':hashlib.sha256(data).hexdigest()}
(directory/'invocation.json').write_text(json.dumps(record,indent=2)+'\n')
sys.stdout.buffer.write(p.stdout);sys.stderr.buffer.write(p.stderr)
raise SystemExit(p.returncode)
'''


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(command, cwd, label, env, timeout=120):
    start=time.monotonic()
    with (cwd/(label+'.stdout.txt')).open('wb') as stdout, (cwd/(label+'.stderr.txt')).open('wb') as stderr:
        process=subprocess.Popen([str(x) for x in command],cwd=cwd,env=env,stdout=stdout,stderr=stderr,start_new_session=True)
        timed_out=False
        try: code=process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out=True;os.killpg(process.pid,signal.SIGKILL);code=process.wait()
    result={'command':[str(x) for x in command],'returncode':code,'timeout':timed_out,'wall_seconds':time.monotonic()-start}
    (cwd/(label+'.result.json')).write_text(json.dumps(result,indent=2)+'\n')
    return result


def checked_c(loop, transpile):
    result=[]; site=0
    for line in transpile(loop).splitlines():
        match=re.match(r'\s*u\[([^\]]+)\]\[([^\]]+)\]\s*=\s*(.*);\s*$',line)
        if match:
            rhs=re.sub(r'u\[([^\]]+)\]\[([^\]]+)\]',r'rd(\1,\2)',match[3])
            result.append('wr(%d,%s,%s,%s);'%(site,match[1],match[2],rhs));site+=1
        else: result.append(line)
    if not site: raise ValueError('no periodic assignments found')
    return '\n'.join(result),site


def harness(source,optimized,transpile,helpers):
    adapted,adapted_sites=checked_c(source,transpile)
    final,final_sites=checked_c(optimized,transpile)
    code=r'''
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <string.h>
#define NX 270
#define VX 40
#define min(a,b) ((a)<(b)?(a):(b))
#define max(a,b) ((a)>(b)?(a):(b))
static long long u[2][NX],expected[2][NX];
static int versions[2][NX],reference_versions[2][NX],mode,N_active,T_active;
static long long reads[2][NX][VX][3],pending[3];
static int pending_count,site_buffers[256],phase_partition_failures;
static long long rd(long long b,long long i) {
  if(b<0||b>1||i<0||i>=N_active||pending_count>=3) exit(20);
  pending[pending_count++]=(b*NX+i)*VX+versions[b][i];
  return u[b][i];
}
static void wr(int site,long long b,long long i,long long value) {
  if(b<0||b>1||i<0||i>=N_active||pending_count!=3) exit(21);
  if(mode==2){if(site<0||site>=256)exit(26);site_buffers[site]|=1<<b;}
  int v=versions[b][i]+1;
  if(v>=VX)exit(22);
  for(int x=0;x<3;x++)for(int y=x+1;y<3;y++)if(pending[x]>pending[y]){
    long long tmp=pending[x];pending[x]=pending[y];pending[y]=tmp;
  }
  for(int x=0;x<3;x++) {
    if(mode==0)reads[b][i][v][x]=pending[x];
    else if(reads[b][i][v][x]!=pending[x])exit(23);
  }
  if(mode&&v>reference_versions[b][i])exit(24);
  u[b][i]=value;versions[b][i]=v;pending_count=0;
}
static void init(int N,int T) {
  memset(versions,0,sizeof versions);memset(site_buffers,0,sizeof site_buffers);pending_count=0;N_active=N;T_active=T;
  for(int b=0;b<2;b++)for(int i=0;i<N;i++)u[b][i]=(T>=20)?0:(b*7+i%11+1);
}
static void reference(long long T,long long N) {
  for(long long t=1;t<T;t++)for(long long i=0;i<N;i++)
    wr(0,t%2,i,rd((t-1)%2,i==0?N-1:i-1)+rd((t-1)%2,i)+rd((t-1)%2,i==N-1?0:i+1));
}
'''+helpers+'\nstatic void adapted(long long T,long long N){\n'+adapted+'\n}\nstatic void optimized(long long T,long long N){\n'+final+r'''
}
static void sample(int T,int N) {
  mode=0;init(N,T);reference(T,N);
  memcpy(expected,u,sizeof u);memcpy(reference_versions,versions,sizeof versions);
  for(mode=1;mode<=2;mode++){
    init(N,T);if(mode==1)adapted(T,N);else optimized(T,N);
    for(int b=0;b<2;b++)for(int i=0;i<N;i++)
      if(u[b][i]!=expected[b][i]||versions[b][i]!=reference_versions[b][i])exit(25);
  }
  int partition=1;
  for(int s=0;s<256;s++)if(site_buffers[s]==3)partition=0;
  if(!partition)phase_partition_failures++;
  printf("T=%d N=%d physical_buffers=true selected_read_versions=true writes_once=true final_values=true phase_partition_sites=%s\n",T,N,partition?"true":"false");
}
int main(void){
  int ns[]={0,1,2,3,31,32,33,63,64,65,257,259};
  int ts[]={0,1,2,3,4,5,8,12};
  for(int t=0;t<8;t++)for(int n=0;n<12;n++)sample(ts[t],ns[n]);
  int large_ts[]={31,32,33,63,64,65};
  for(int t=0;t<6;t++)for(int n=31;n<=33;n++)sample(large_ts[t],n);
  printf("phase_partition_failures=%d\n",phase_partition_failures);
  return 0;
}
'''
    return code,adapted_sites,final_sites


def harness_2d(source,optimized,transpile,helpers):
    def checked(loop):
        result=[];sites=0
        text=re.sub(r'(?m)^[ \t]*u\[.*?;',lambda m:' '.join(m[0].split()),transpile(loop),flags=re.S)
        for line in text.splitlines():
            match=re.match(r'\s*u\[([^\]]+)\]\[([^\]]+)\]\[([^\]]+)\]\s*=\s*(.*);\s*$',line)
            if match:
                rhs=re.sub(r'u\[([^\]]+)\]\[([^\]]+)\]\[([^\]]+)\]',r'rd(\1,\2,\3)',match[4])
                result.append('wr(%d,%s,%s,%s,%s);'%(sites,match[1],match[2],match[3],rhs));sites+=1
            else:result.append(line)
        if not sites:raise ValueError('no 2D periodic assignments found')
        return '\n'.join(result),sites
    adapted,adapted_sites=checked(source);final,final_sites=checked(optimized)
    code=r'''
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <string.h>
#define NX 66
#define VX 40
#define min(a,b) ((a)<(b)?(a):(b))
#define max(a,b) ((a)>(b)?(a):(b))
static long long u[2][NX][NX],expected[2][NX][NX];
static int versions[2][NX][NX],reference_versions[2][NX][NX],mode,N_active;
static long long reads[2][NX][NX][VX][5],pending[5];
static int pending_count,site_buffers[256],phase_partition_failures;
static long long rd(long long b,long long i,long long j){
  if(b<0||b>1||i<0||i>=N_active||j<0||j>=N_active||pending_count>=5)exit(20);
  pending[pending_count++]=((b*NX+i)*NX+j)*VX+versions[b][i][j];
  return u[b][i][j];
}
static void wr(int site,long long b,long long i,long long j,long long value){
  if(b<0||b>1||i<0||i>=N_active||j<0||j>=N_active||pending_count!=5)exit(21);
  if(mode==2){if(site<0||site>=256)exit(26);site_buffers[site]|=1<<b;}
  int v=versions[b][i][j]+1;if(v>=VX)exit(22);
  for(int x=0;x<5;x++)for(int y=x+1;y<5;y++)if(pending[x]>pending[y]){
    long long tmp=pending[x];pending[x]=pending[y];pending[y]=tmp;
  }
  for(int x=0;x<5;x++){
    if(mode==0)reads[b][i][j][v][x]=pending[x];
    else if(reads[b][i][j][v][x]!=pending[x])exit(23);
  }
  if(mode&&v>reference_versions[b][i][j])exit(24);
  u[b][i][j]=value;versions[b][i][j]=v;pending_count=0;
}
static void init(int N,int T){
  memset(versions,0,sizeof versions);memset(site_buffers,0,sizeof site_buffers);pending_count=0;N_active=N;
  for(int b=0;b<2;b++)for(int i=0;i<N;i++)for(int j=0;j<N;j++)u[b][i][j]=(T>=20)?0:(b*7+i%11+j%3+1);
}
static void reference(long long T,long long N){
  for(long long t=1;t<T;t++)for(long long i=0;i<N;i++)for(long long j=0;j<N;j++)
    wr(0,t%2,i,j,rd((t-1)%2,i==0?N-1:i-1,j)+rd((t-1)%2,i,j)
      +rd((t-1)%2,i==N-1?0:i+1,j)
      +rd((t-1)%2,i==0?N-1:i-1,j==0?N-1:j-1)
      +rd((t-1)%2,i==N-1?0:i+1,j==N-1?0:j+1));
}
'''+helpers+'\nstatic void adapted(long long T,long long N){\n'+adapted+'\n}\nstatic void optimized(long long T,long long N){\n'+final+r'''
}
static void sample(int T,int N){
  mode=0;init(N,T);reference(T,N);
  memcpy(expected,u,sizeof u);memcpy(reference_versions,versions,sizeof versions);
  for(mode=1;mode<=2;mode++){
    init(N,T);if(mode==1)adapted(T,N);else optimized(T,N);
    for(int b=0;b<2;b++)for(int i=0;i<N;i++)for(int j=0;j<N;j++)
      if(u[b][i][j]!=expected[b][i][j]||versions[b][i][j]!=reference_versions[b][i][j])exit(25);
  }
  int partition=1;for(int s=0;s<256;s++)if(site_buffers[s]==3)partition=0;
  if(!partition)phase_partition_failures++;
  printf("T=%d N=%d physical_buffers=true selected_read_versions=true writes_once=true final_values=true phase_partition_sites=%s\n",T,N,partition?"true":"false");
}
int main(void){
  int ns[]={0,1,2,3,31,32,33,63,64,65},ts[]={0,1,2,3,4,5,8,12};
  for(int t=0;t<8;t++)for(int n=0;n<10;n++)sample(ts[t],ns[n]);
  int large_ts[]={31,32,33,63,64,65};
  for(int t=0;t<6;t++)for(int n=1;n<=3;n++)sample(large_ts[t],n);
  printf("phase_partition_failures=%d\n",phase_partition_failures);return 0;
}
'''
    return code,adapted_sites,final_sites


def split_assignment(line):
    """Return (indent, array, subscripts, rhs) for `a[e0][e1]... = rhs;`."""
    match=re.match(r'(\s*)([A-Za-z_]\w*)\[',line)
    if not match:return None
    position=match.end()-1;subscripts=[]
    while position<len(line) and line[position]=='[':
        depth=0
        for end in range(position,len(line)):
            depth+=(line[end]=='[')-(line[end]==']')
            if depth==0:break
        else:return None
        subscripts.append(line[position+1:end]);position=end+1
    assignment=re.match(r'\s*=(?!=)\s*(.*);\s*$',line[position:])
    return (match[1],match[2],subscripts,assignment[1]) if assignment else None


def logical_lines(code):
    """Join a multi-line assignment of transpiled C into one line."""
    result=[];pending=None
    for line in code.splitlines():
        if pending is not None:
            pending+=' '+line.strip()
            if pending.rstrip().endswith(';'):result.append(pending);pending=None
            continue
        if re.match(r'\s*[A-Za-z_]\w*\[',line) and not line.rstrip().endswith((';','{','}')):
            pending=line.rstrip();continue
        result.append(line)
    if pending is not None:raise ValueError('unterminated assignment')
    return result


def phase_harness(source,optimized,transpile,helpers):
    """Generic observer for phase-form periodic inputs (t = 2q + p [+ 1]).

    The first subscript of every array selects one of two physical buffers.
    Each sample runs the source and the candidate from the same initial
    buffers and requires bitwise-equal buffers and equal write counts per
    cell. Phase partition: every assignment site of the candidate writes a
    single buffer, and the executed sites together write both buffers.
    """
    context=re.search(r'^\s*context\(([^)]*)\)',source,re.M)
    if not context:raise ValueError('periodic input has no context')
    parameters=[name.strip() for name in context[1].split(',') if name.strip()]
    if 'T' not in parameters or len(parameters)<2:raise ValueError('expected time parameter T and a size parameter')
    arrays={}
    for line in logical_lines(transpile(source)):
        found=split_assignment(line)
        if found:arrays.setdefault(found[1],len(found[2]))
    if not arrays or min(arrays.values())<2 or max(arrays.values())>4:
        raise ValueError('expected double-buffered arrays of rank 2 to 4')
    spatial=max(arrays.values())-1
    sizes={1:[1,2,3,5,31,32,33,65],2:[1,2,3,5,31,33],3:[1,2,3,5,17]}[spatial]
    times={1:[0,1,2,3,4,5,8,64,65,66,67],2:[0,1,2,3,4,5,8,64,65,66,67],3:[0,1,2,3,5,64,67]}[spatial]
    extent=2*max(sizes)+2
    element='double' if re.search(r'\d\.\d',source) else 'unsigned long long'
    names=list(arrays)

    def instrumented(text):
        lines=[];sites=0
        for line in logical_lines(transpile(text)):
            found=split_assignment(line)
            if found:
                indent,array,subscripts,_=found
                if array not in arrays or len(subscripts)!=arrays[array]:raise ValueError('unexpected assignment target '+array)
                coordinates=(subscripts+['0']*4)[:4]
                arguments=','.join('(long long)(%s)'%c for c in coordinates)
                lines.append('%s{ wr(%d,%d,%s); %s }'%(indent,sites,names.index(array),arguments,line.strip()));sites+=1
            else:lines.append(line)
        return '\n'.join(lines),sites

    original,original_sites=instrumented(source)
    final,final_sites=instrumented(optimized)
    if final_sites<2 or final_sites<=original_sites or final_sites>4096:
        raise ValueError('expected split assignment sites, got %d'%final_sites)
    shape=lambda array:'[2]'+'[%d]'%extent*(arrays[array]-1)
    index=lambda array,prefix='':'[b]'+''.join('[%s]'%v for v in 'xyz'[:arrays[array]-1])
    loops=lambda array:''.join('for(long long %s=0;%s<%d;%s++)'%(v,v,extent,v) for v in 'xyz'[:arrays[array]-1])
    signature=', '.join('long long '+name for name in parameters)
    call=', '.join('T' if name=='T' else 'S' for name in parameters)
    code='#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n#include <limits.h>\n'
    code+='#define min(a,b) ((a)<(b)?(a):(b))\n#define max(a,b) ((a)>(b)?(a):(b))\n'
    code+='static int mode,site_buffers[4096],seen_buffers;\n'
    for array in names:
        code+='static %s %s%s,%s_expected%s;\nstatic int %s_writes%s,%s_expected_writes%s;\n'%(
            element,array,shape(array),array,shape(array),array,shape(array),array,shape(array))
    code+='static void wr(int site,int id,long long b,long long x,long long y,long long z){\n'
    code+='  if(b<0||b>1||x<0||x>=%d||y<0||y>=%d||z<0||z>=%d)exit(31);\n'%(extent,extent,extent)
    code+='  if(mode){site_buffers[site]|=1<<b;seen_buffers|=1<<b;}\n  switch(id){\n'
    for number,array in enumerate(names):
        code+='  case %d:%s_writes%s++;break;\n'%(number,array,index(array))
    code+='  default:exit(32);\n  }\n}\n'
    code+='static void init(void){\n'
    for number,array in enumerate(names):
        value=('(double)((b*7+%d*3+x*5+y*3+z)%%17)*0.25+1.0' if element=='double' else '(unsigned long long)((b*131+%d*17+x*7+y*3+z+1)%%1009)')%number
        body='%s%s=%s;'%(array,index(array),value)
        code+='  for(long long b=0;b<2;b++)%s{long long y=0,z=0;(void)y;(void)z;%s}\n'%(loops(array),body) if arrays[array]==2 else \
              '  for(long long b=0;b<2;b++)%s{long long z=0;(void)z;%s}\n'%(loops(array),body) if arrays[array]==3 else \
              '  for(long long b=0;b<2;b++)%s{%s}\n'%(loops(array),body)
        code+='  memset(%s_writes,0,sizeof %s_writes);\n'%(array,array)
    code+='}\n'+helpers
    code+='\nstatic void original(%s) {\n%s\n}\nstatic void optimized(%s) {\n%s\n}\n'%(signature,original,signature,final)
    code+='int main(void){\n  long long times[]={%s},sizes[]={%s};int samples=0;\n'%(','.join(map(str,times)),','.join(map(str,sizes)))
    code+='  for(int t=0;t<%d;t++)for(int s=0;s<%d;s++){\n    long long T=times[t],S=sizes[s];\n'%(len(times),len(sizes))
    code+='    mode=0;init();original(%s);\n'%call
    for array in names:
        code+='    memcpy(%s_expected,%s,sizeof %s);memcpy(%s_expected_writes,%s_writes,sizeof %s_writes);\n'%((array,)*6)
    code+='    memset(site_buffers,0,sizeof site_buffers);mode=1;init();optimized(%s);\n'%call
    for array in names:
        code+='    if(memcmp(%s_expected,%s,sizeof %s))return 33;\n    if(memcmp(%s_expected_writes,%s_writes,sizeof %s_writes))return 34;\n'%((array,)*6)
    code+='    for(int site=0;site<%d;site++)if(site_buffers[site]==3)return 35;\n'%final_sites
    code+='    printf("T=%lld S=%lld exact_values=true writes_once=true phase_partition_sites=true\\n",T,S);samples++;\n  }\n'
    code+='  if(seen_buffers!=3)return 36;\n  return 0;\n}\n'
    return code,final_sites,len(times)*len(sizes)


def review_split_calls(rows,root,polopt,env):
    for row in rows:
        for call in row['invocations']:
            if '--iss' not in call['command'] or not call['after_iss_marker']:
                continue
            directory=Path(call['path'])
            recovered=run([sys.executable,root/'tools/iss/pluto_iss_check.py','--emit-bridge-from-combined',directory/'stdout.txt'],directory,'bridge-review',env)
            text=(directory/'bridge-review.stdout.txt').read_text()
            call['bridge_recovery']=recovered
            if recovered['returncode']==0:
                call['bridge_counts']={k:int(v) for k,v in re.findall(r'^(BEFORE_STMTS|AFTER_STMTS|CUTS)\s+(\d+)',text,re.M)}
                call['bridge_validation']=run([polopt,'--validate-iss-bridge',directory/'bridge-review.stdout.txt'],directory,'bridge-check',env)
        row['producer_split']=any(c.get('bridge_counts',{}).get('AFTER_STMTS',0)>c.get('bridge_counts',{}).get('BEFORE_STMTS',0) for c in row['invocations'])
        targets=[c['bridge_counts']['AFTER_STMTS'] for c in row['invocations']
                 if c.get('bridge_counts',{}).get('AFTER_STMTS',0)>c.get('bridge_counts',{}).get('BEFORE_STMTS',0)]
        row['split_forwarded']=bool(targets and any('--iss' not in c['command'] and c['input_statements'] in targets for c in row['invocations']))
    return rows


def official_bridges(root,polopt,pluto,output):
    rows=[];env=dict(os.environ,COMPCERT_CONFIG=str(root/'tests/pluto/polcert.ini'))
    expected={'jacobi-1d-periodic':(1,2,1),'jacobi-3d-periodic':(1,4,2),'multi-stmt-2d-periodic':(2,8,2)}
    for name,counts in expected.items():
        directory=output/name;directory.mkdir(parents=True,exist_ok=False)
        source=pluto.parent.parent/'test'/(name+'.c');copy=directory/'input.c';copy.write_bytes(source.read_bytes())
        producer=run([pluto,'--pet','--iss','--identity','--notile','--noparallel','--moredebug','--silent',copy],directory,'pluto',env)
        bridge=run([sys.executable,root/'tools/iss/pluto_iss_check.py','--emit-bridge-from-combined',directory/'pluto.stdout.txt'],directory,'bridge',env)
        measured={k:int(v) for k,v in re.findall(r'^(BEFORE_STMTS|AFTER_STMTS|CUTS)\s+(\d+)',(directory/'bridge.stdout.txt').read_text(),re.M)}
        check=run([polopt,'--validate-iss-bridge',directory/'bridge.stdout.txt'],directory,'check',env) if bridge['returncode']==0 else None
        passed=bool(producer['returncode']==0 and bridge['returncode']==0 and check and check['returncode']==0 and tuple(measured.get(k) for k in ['BEFORE_STMTS','AFTER_STMTS','CUTS'])==counts)
        rows.append({'kernel':name,'category':'standalone_iss_witness','native_end_to_end':False,'source':str(source),'source_sha256':digest(source),'producer':producer,'bridge':bridge,'check':check,'counts':measured,'passed':passed})
        print(name,measured,passed,flush=True)
    (output/'summary.json').write_text(json.dumps({'rows':rows,'provenance':{str(p):digest(p) for p in [polopt,pluto,root/'tools/iss/pluto_iss_check.py',Path(__file__)]}},indent=2)+'\n')
    return 0 if all(r['passed'] for r in rows) else 1


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root',type=Path,default=Path(__file__).resolve().parents[2])
    parser.add_argument('--fixtures',type=Path)
    parser.add_argument('--polopt',type=Path)
    parser.add_argument('--pluto',type=Path,default=Path(os.environ.get('POLCERT_PLUTO','/pluto/tool/pluto')))
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--kernels',nargs='+',default=['jacobi_1d_periodic_phase','jacobi_1d_periodic_guards'])
    parser.add_argument('--review-existing',action='store_true')
    parser.add_argument('--official-bridges',action='store_true')
    parser.add_argument('--require-retained',action='store_true')
    args=parser.parse_args();root=args.source_root.resolve();output=args.output.resolve();output.mkdir(parents=True,exist_ok=True)
    fixtures=(args.fixtures or root/'tests/iss-native').resolve();polopt=(args.polopt or root/'polopt').resolve()
    if args.official_bridges:
        return official_bridges(root,polopt,args.pluto.resolve(),output)
    sys.path.insert(0,str(root/'tools/end_to_end_c'))
    from loop_to_c import transpile_loop_text,INTEGER_HELPERS_C
    from runner_common import extract_optimized_loop
    if args.review_existing:
        data=json.loads((output/'summary.json').read_text())
        env=dict(os.environ,COMPCERT_CONFIG=str(root/'tests/pluto/polcert.ini'))
        data['rows']=review_split_calls(data['rows'],root,polopt,env)
        (output/'reviewed-summary.json').write_text(json.dumps(data,indent=2)+'\n')
        print(json.dumps([{r['kernel']:[c['bridge_counts'] for c in r['invocations'] if '--iss' in c['command']]} for r in data['rows']]),flush=True)
        return 0
    wrapper=output/'pluto-record';wrapper.write_text(WRAPPER);wrapper.chmod(0o755)
    rows=[]
    for name in args.kernels:
        directory=output/name;directory.mkdir(exist_ok=False)
        source=fixtures/(name+'.loop');(directory/'input.loop').write_bytes(source.read_bytes())
        helper=directory/'tools/iss/pluto_iss_check.py';helper.parent.mkdir(parents=True)
        helper.write_bytes((root/'tools/iss/pluto_iss_check.py').read_bytes())
        env=dict(os.environ,COMPCERT_CONFIG=str(root/'tests/pluto/polcert.ini'),POLCERT_PLUTO=str(wrapper),ISS_REAL_PLUTO=str(args.pluto),ISS_PERIODIC_LOG=str(directory/'pluto'))
        result=run([polopt,'--iss',source],directory,'compile',env)
        rank=2 if name.startswith('jacobi_2d_') else 1
        row={'kernel':name,'original_kernel':f'/pluto/test/jacobi-{rank}d-periodic.c','source_sha256':digest(source),'compile':result}
        calls=[]
        for call in sorted((directory/'pluto').glob('*/invocation.json')):
            record=json.loads(call.read_text());text=(call.parent/'stdout.txt').read_text(errors='replace')
            record['bridge_counts']={k:int(v) for k,v in re.findall(r'^(BEFORE_STMTS|AFTER_STMTS|CUTS)\s+(\d+)',text,re.M)}
            record['after_iss_marker']='After ISS' in text;record['path']=str(call.parent)
            calls.append(record)
        row['invocations']=calls
        review_split_calls([row],root,polopt,env)
        if result['returncode']==0:
            optimized=extract_optimized_loop((directory/'compile.stdout.txt').read_text())
            (directory/'optimized.loop').write_text(optimized)
            check_harness=harness_2d if rank==2 else harness
            code,original_sites,final_sites=check_harness(source.read_text(),optimized,transpile_loop_text,INTEGER_HELPERS_C)
            (directory/'check.c').write_text(code)
            build=run(['cc','-O0','-std=c99',directory/'check.c','-o',directory/'check'],directory,'cc',env)
            checked=run([directory/'check'],directory,'check',env,30) if build['returncode']==0 else None
            row.update(adapted_sites=original_sites,final_sites=final_sites,build=build,check=checked,
                       complete_samples=(98 if rank==2 else 114) if checked and checked['returncode']==0 else 0,
                       physical_access_and_value_checks_passed=bool(checked and checked['returncode']==0))
            partition=re.search(r'phase_partition_failures=(\d+)',(directory/'check.stdout.txt').read_text()) if checked else None
            row['phase_partition_failures']=int(partition[1]) if partition else None
            row['native_iss_effect_retained']=bool(row['producer_split'] and row['split_forwarded'] and partition and int(partition[1])==0 and row['physical_access_and_value_checks_passed'])
        rows.append(row)
        (output/'summary.json').write_text(json.dumps({'rows':rows,'provenance':{str(p):digest(p) for p in [polopt,args.pluto,root/'tools/iss/pluto_iss_check.py',Path(__file__)]}},indent=2)+'\n')
        print(json.dumps({k:row.get(k) for k in ['kernel','producer_split','adapted_sites','final_sites','complete_samples','physical_access_and_value_checks_passed']}),flush=True)
    passed = all(r.get('physical_access_and_value_checks_passed') for r in rows)
    if args.require_retained:
        passed = passed and all(r.get('native_iss_effect_retained') for r in rows)
    return 0 if passed else 1


if __name__=='__main__':
    raise SystemExit(main())
