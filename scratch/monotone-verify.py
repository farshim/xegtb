# Independent check of the 10x10 monotone drive: recompute the net from
# scratch after every ply and confirm it never grows, and that the final
# position really traps the black king.
from collections import deque
F="abcdefghijklmnopqrstuvwxyz"
n=10
def sq(s): return (F.index(s[0]), int(s[1:])-1)
def nm(p): return F[p[0]]+str(p[1]+1)
def cheb(a,b): return max(abs(a[0]-b[0]),abs(a[1]-b[1]))
def net(W,b):
    free=lambda s: 0<=s[0]<n and 0<=s[1]<n and all(cheb(s,w)>=2 for w in W)
    if not free(b): return 0
    seen={b}; dq=deque([b])
    while dq:
        x,y=dq.popleft()
        for dx in(-1,0,1):
            for dy in(-1,0,1):
                t=(x+dx,y+dy)
                if t not in seen and free(t): seen.add(t); dq.append(t)
    return len(seen)
W=[sq(s) for s in "a1 j1 a10 j10".split()]; b=sq("e5")
wm="Ka1-b2 Kj1-i2 Ka10-b9 Kj10-i9 Kb2-c2 Kc2-d2 Kd2-e2 Ke2-f2 Ki2-i3 Ki3-i4 Ki9-i8 Ki4-h5 Kh5-g5 Kf2-e2 Kb9-c8 Kc8-d7 Kd7-e8 Ki8-h9 Kg5-f5 Ke2-d2 Kf5-e5 Kd2-c2 Ke5-d5 Kd5-c5 Kc5-b4 Kb4-a3".split()
bm="e5-d4 d4-c4 c4-b4 b4-a4 a4-a3 a3-a2 a2-a1 a1-a2 a2-a1 a1-a2 a2-a1 a1-a2 a2-a1 a1-a2 a2-a1 a1-a2 a2-a1 a1-a2 a2-a1 a1-a2 a2-a1 a1-a2 a2-a1 a1-a2 a2-a1".split()
prev=net(W,b); print("start net",prev)
grew=0; moves=0; shrinks=[]
for i,w in enumerate(wm):
    a,c=w[1:].split("-"); a,c=sq(a),sq(c)
    assert a in W and cheb(a,c)==1 and c not in W and c!=b, ("illegal white move",w)
    W[W.index(a)]=c; moves+=1
    v=net(W,b)
    if v>prev: grew+=1
    if v<prev: shrinks.append(moves)
    prev=v
    if v==1: print("net closed after",moves,"white moves"); break
    assert v>=1, "net opened: black could capture"
    if i<len(bm):
        a,c=bm[i].split("-"); a,c=sq(a),sq(c)
        assert b==a and cheb(a,c)==1 and c not in W, ("illegal black move",bm[i])
        b=c
        assert net(W,b)==v, "black changed the net"
print("white moves:",moves," times the net grew:",grew)
gaps=[shrinks[0]]+[shrinks[i]-shrinks[i-1] for i in range(1,len(shrinks))]
print("white moves between shrinks:",gaps,"  worst",max(gaps))
# the final trap
print("final white kings:",sorted(nm(w) for w in W),"black king:",nm(b))
esc=[]
for dx in(-1,0,1):
    for dy in(-1,0,1):
        if dx==dy==0: continue
        t=(b[0]+dx,b[1]+dy)
        if 0<=t[0]<n and 0<=t[1]<n:
            esc.append((nm(t), "captured" if any(cheb(t,w)<=1 for w in W) else "ESCAPES"))
print("black's replies:",esc)
