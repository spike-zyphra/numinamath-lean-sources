import Mathlib

/- The red parabola shown is the graph of the equation $x = ay^2 + by + c$.  Find $c$.  (The grid lines are spaced one unit apart.)

[asy]
size(150);
real ticklen=3;
real tickspace=2;

real ticklength=0.1cm;
real axisarrowsize=0.14cm;
pen axispen=black+1.3bp;
real vectorarrowsize=0.2cm;
real tickdown=-0.5;
real tickdownlength=-0.15inch;
real tickdownbase=0.3;
real wholetickdown=tickdown;
void rr_cartesian_axes(real xleft, real xright, real ybottom, real ytop, real xstep=1, real ystep=1, bool

useticks=false, bool complexplane=false, bool usegrid=true) {

import graph;

real i;

if(complexplane) {

label("$\textnormal{Re}$",(xright,0),SE);

label("$\textnormal{Im}$",(0,ytop),NW);

} else {

label("$x$",(xright+0.4,-0.5));

label("$y$",(-0.5,ytop+0.2));

}

ylimits(ybottom,ytop);

xlimits( xleft, xright);

real[] TicksArrx,TicksArry;

for(i=xleft+xstep; i<xright; i+=xstep) {

if(abs(i) >0.1) {

TicksArrx.push(i);

}

}

for(i=ybottom+ystep; i<ytop; i+=ystep) {

if(abs(i) >0.1) {

TicksArry.push(i);

}

}

if(usegrid) {

xaxis(BottomTop(extend=false), Ticks("%", TicksArrx ,pTick=gray

(0.22),extend=true),p=invisible);//,above=true);

yaxis(LeftRight(extend=false),Ticks("%", TicksArry ,pTick=gray(0.22),extend=true),

p=invisible);//,Arrows);

}

if(useticks) {

xequals(0, ymin=ybottom, ymax=ytop, p=axispen, Ticks("%",TicksArry ,

pTick=black+0.8bp,Size=ticklength), above=true, Arrows(size=axisarrowsize));

yequals(0, xmin=xleft, xmax=xright, p=axispen, above=true, Arrows(size=axisarrowsize));

} else {

xequals(0, ymin=ybottom, ymax=ytop, p=axispen, above=true, Arrows(size=axisarrowsize));

yequals(0, xmin=xleft, xmax=xright, p=axispen, above=true, Arrows(size=axisarrowsize));

}
};
real lowerx, upperx, lowery, uppery;
real f(real x) {return (x-2)*(x-2)/2-4;}
lowery = -2;
uppery = 6;
rr_cartesian_axes(-5,4,lowery,uppery);
draw(reflect((0,0),(1,1))*(graph(f,lowery,uppery,operator ..)), red);
[/asy] -/
theorem algebra_11425 {a b c : ℝ} (ha : a ≠ 0) (h : ∀ x y, x = a * y ^ 2 + b * y + c → (x - 2) * (x - 2) / 2 - 4 = y) :
    c = -2 := by
  have h1 := h (a * (-4)^2 + b * (-4) + c) (-4) (by ring)
  have h2 := h (a * 0 ^ 2 + b * 0 + c) 0 (by 
    ring
  )
  ring_nf at h1 h2 
  have h3 := h (a * 2 ^ 2 + b * 2 + c) 2 (by 
    ring
  )
  ring_nf at h3
  have h4 := h (a * 1 ^ 2 + b * 1 + c) 1 (by 
    ring
  )
  ring_nf at h4
  have h5 := h (a * 4 ^ 2 + b * 4 + c) 4 (by 
    ring
  )
  ring_nf at h5
  have h6 := h (a * 3 ^ 2 + b * 3 + c) 3 (by 
    ring
  )
  ring_nf at h6 
  have h7 := h (a * (-1) ^ 2 + b * (-1) + c) (-1) (by 
    ring
  )
  ring_nf at h7
  have h8 := h (a * (-2) ^ 2 + b * (-2) + c) (-2) (by
    ring
  )
  ring_nf at h8
  ring_nf at h1 h2 h3 h4 h5 h6 h7 h8
  nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by assumption)]