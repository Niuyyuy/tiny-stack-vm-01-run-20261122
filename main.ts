// Tiny stack VM: faithful interpreter of make.fun's tiny stack ISA v1.
// One run answers every instance: reads program.bin + input.bin per id, writes
// stdout.bin + exit.txt. 32-bit wrapping arithmetic, 256-value data stack,
// 64-entry call stack, 256 words of memory, ten traps with their own exit
// codes, a 1,000,000 step limit and a 65,536 byte output limit.
import {existsSync,mkdirSync,readdirSync,readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
// Opcode byte -> [immediate bytes, values popped, values pushed]; absent = trap 5.
const M=new Map([[0,[0,0,0]],[1,[1,0,1]],[2,[4,0,1]],[3,[0,1,0]],[4,[0,1,2]],[5,[0,2,2]],[6,[0,2,3]],[7,[0,3,3]],[16,[0,2,1]],[17,[0,2,1]],[18,[0,2,1]],[19,[0,2,1]],[20,[0,2,1]],[21,[0,2,1]],[22,[0,2,1]],[23,[0,1,1]],[24,[0,2,1]],[25,[0,2,1]],[26,[0,2,1]],[27,[0,1,1]],[28,[0,2,1]],[29,[0,2,1]],[30,[0,2,1]],[32,[0,2,1]],[33,[0,2,1]],[34,[0,2,1]],[48,[2,0,0]],[49,[2,1,0]],[50,[2,1,0]],[51,[2,0,0]],[52,[0,0,0]],[64,[0,1,1]],[65,[0,2,0]],[80,[0,1,0]],[81,[0,1,0]],[82,[0,0,1]],[83,[0,1,0]]]);
const E=new TextEncoder();
function run(p,q){
  const n=p.length,D=new Int32Array(256);let s=0;
  const C=new Int32Array(64);let c=0;
  const Y=new Int32Array(256),O=new Uint8Array(65536);
  let o=0,i=0,pc=0,st=0;
  const done=x=>({out:O.slice(0,o),code:x});
  for(;;){
    if(st===1e6)return done(10); // step limit
    if(pc<0||pc>=n)return done(9); // pc outside the program
    const op=p[pc],m=M.get(op);
    if(m===undefined)return done(5); // unknown opcode
    const im=m[0],po=m[1],pu=m[2];
    if(pc+im>=n)return done(9); // immediate cut off by the program's end
    st++;
    const nx=pc+1+im;
    if(s<po)return done(2); // stack underflow
    if(s-po+pu>256)return done(3); // stack overflow
    pc=nx;
    switch(op){
      case 0:return done(0); // HALT
      case 1:D[s++]=(p[nx-1]<<24)>>24;break; // PUSH8 sign-extended
      case 2:D[s++]=p[nx-4]|p[nx-3]<<8|p[nx-2]<<16|p[nx-1]<<24;break; // PUSH32
      case 3:s--;break; // POP
      case 4:D[s]=D[s-1];s++;break; // DUP
      case 5:{const x=D[s-1],y=D[s-2];D[s-1]=y;D[s-2]=x;break;} // SWAP
      case 6:D[s]=D[s-2];s++;break; // OVER
      case 7:{const x=D[s-3],y=D[s-2],z=D[s-1];D[s-3]=y;D[s-2]=z;D[s-1]=x;break;} // ROT
      case 23:D[s-1]=-D[s-1]|0;break; // NEG wraps
      case 27:D[s-1]=~D[s-1];break; // NOT
      case 16:case 17:case 18:case 19:case 20:case 21:case 22:case 24:case 25:case 26:case 28:case 29:case 30:case 32:case 33:case 34:{
        const b=D[s-1],a=D[s-2];let r;
        if(op===16)r=a+b|0; // ADD wraps
        else if(op===17)r=a-b|0; // SUB wraps
        else if(op===18)r=Math.imul(a,b); // MUL low 32 bits exactly
        else if(op===19){if(!b)return done(4);r=a===-2147483648&&b===-1?a:a/b|0;} // DIV truncates
        else if(op===20){if(!b)return done(4);r=b===-1?0:a%b|0;} // MOD sign of a
        else if(op===21){if(!b)return done(4);r=Math.floor((a>>>0)/(b>>>0))|0;} // DIVU
        else if(op===22){if(!b)return done(4);r=(a>>>0)%(b>>>0)|0;} // MODU
        else if(op===24)r=a&b;
        else if(op===25)r=a|b;
        else if(op===26)r=a^b;
        else if(op===28)r=a<<(b&31); // SHL low 5 bits of count
        else if(op===29)r=a>>(b&31); // SHR arithmetic
        else if(op===30)r=(a>>>(b&31))|0; // SHRU logical
        else if(op===32)r=a===b?1:0;
        else if(op===33)r=a<b?1:0;
        else r=(a>>>0)<(b>>>0)?1:0; // LTU unsigned
        s-=2;D[s++]=r;break;}
      case 48:case 49:case 50:{ // JMP / JZ / JNZ
        const rel=(p[nx-2]|p[nx-1]<<8)<<16>>16;
        let t=1;
        if(op!==48){const v=D[--s];t=op===49?v===0:v!==0;}
        if(t)pc=nx+rel; // target unchecked: traps 9 next step if outside
        break;}
      case 51: // CALL
        if(c===64)return done(7);
        C[c++]=nx;pc=p[nx-2]|p[nx-1]<<8;break;
      case 52: // RET
        if(!c)return done(8);
        pc=C[--c];break;
      case 64:{ // LOAD
        const a=D[s-1];
        if(a<0||a>=256)return done(6);
        D[s-1]=Y[a];break;}
      case 65:{ // STORE (v addr --): addr is the top
        const a=D[s-1],v=D[s-2];
        if(a<0||a>=256)return done(6);
        s-=2;Y[a]=v;break;}
      case 80:{ // PRINT decimal ASCII, no newline
        const g=E.encode(String(D[s-1]));
        if(o+g.length>65536)return done(11);
        s--;O.set(g,o);o+=g.length;break;}
      case 81: // PUTC one byte, v AND 255
        if(o+1>65536)return done(11);
        O[o++]=D[--s]&255;break;
      case 82:D[s++]=i<q.length?q[i++]:-1;break; // IN, -1 once used up
      case 83:return done(D[--s]&255); // EXIT code is v AND 255
    }
  }
}
const I=process.env.MAKEFUN_INPUT_DIR??'/input',O=process.env.MAKEFUN_OUTPUT_DIR??'/output';
for(const id of readdirSync(I).sort()){
  const pr=new Uint8Array(readFileSync(join(I,id,'program.bin')));
  const ip=existsSync(join(I,id,'input.bin'))?new Uint8Array(readFileSync(join(I,id,'input.bin'))):new Uint8Array(0);
  const r=run(pr,ip);
  mkdirSync(join(O,id),{recursive:true});
  writeFileSync(join(O,id,'stdout.bin'),r.out);
  writeFileSync(join(O,id,'exit.txt'),r.code+'\n');
}
