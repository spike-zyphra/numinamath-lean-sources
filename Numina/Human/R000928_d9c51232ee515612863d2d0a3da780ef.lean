import Mathlib

/- Below is a portion of the graph of a function, $y=h(x)$:

[asy]
import graph; size(8cm); real lsf=0.5; pen dps=linewidth(0.7)+fontsize(10); defaultpen(dps); pen ds=black; real xmin=-0.75,xmax=8.25,ymin=-1.25,ymax=10.25;

pen cqcqcq=rgb(0.75,0.75,0.75);

/*grid*/ pen gs=linewidth(0.7)+cqcqcq+linetype("2 2"); real gx=1,gy=1;
for(real i=ceil(xmin/gx)*gx;i<=floor(xmax/gx)*gx;i+=gx) draw((i,ymin)--(i,ymax),gs); for(real i=ceil(ymin/gy)*gy;i<=floor(ymax/gy)*gy;i+=gy) draw((xmin,i)--(xmax,i),gs);

Label laxis; laxis.p=fontsize(10);

xaxis("",xmin,xmax,Ticks(laxis,Step=1.0,Size=2,NoZero),Arrows(6),above=true); yaxis("",ymin,ymax,Ticks(laxis,Step=1.0,Size=2,NoZero),Arrows(6),above=true);
real f1(real x){return (x-0.5)*(x-2.5)*(x-6.5)*(x-7.5)/16+x;}
draw(graph(f1,-0.25,8.25),linewidth(1));
clip((xmin,ymin)--(xmin,ymax)--(xmax,ymax)--(xmax,ymin)--cycle);
label("$y=h(x)$",(8.5,8),E);
[/asy]

What is the sum of all integers $x$ in the interval shown ($0\le x\le 8$) such that $h(x)>x$ ? -/
theorem algebra_19171 {h : ℝ → ℝ} (hf : h = fun x => (x - 0.5) * (x - 2.5) * (x - 6.5) * (x - 7.5) / 16 + x)
    (x : ℕ) (hx : 0 ≤ x ∧ x ≤ 8) : (h x > x ↔ x = 0 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 8) ∧ 0 + 3 + 4 + 5 + 6 + 8 = 26 := by
  constructor
  constructor
  -- If $h(x) > x$, then $x = 0, 3, 4, 5, 6, 8$.
  have hxge := hx.1
  have hxle := hx.2
  -- Since $0 \leq x \leq 8$, we have $x = 0, 1, 2, 3, 4, 5, 6, 7, 8$.
  interval_cases x
  -- $x = 0$.
  simp only [CharP.cast_eq_zero, gt_iff_lt, OfNat.zero_ne_ofNat, or_self, or_false, implies_true]
  simp only [Nat.cast_one, gt_iff_lt, one_ne_zero, OfNat.one_ne_ofNat, or_self, imp_false, not_lt, ge_iff_le]
  -- $x = 1$.
  rw [hf]
  ring_nf
  linarith
  -- $x = 2$.
  simp only [Nat.cast_ofNat, gt_iff_lt, OfNat.ofNat_ne_zero, Nat.reduceEqDiff, or_self, imp_false, not_lt, ge_iff_le]
  rw [hf]
  ring_nf
  linarith
  -- $x = 3$.
  simp only [Nat.cast_ofNat, gt_iff_lt, OfNat.ofNat_ne_zero, Nat.reduceEqDiff, or_self, or_false, or_true, implies_true]
  -- $x = 4$.
  simp only [Nat.cast_ofNat, gt_iff_lt, OfNat.ofNat_ne_zero, Nat.succ_ne_self, Nat.reduceEqDiff, or_self, or_false, or_true, implies_true]
  -- $x = 5$.
  simp only [Nat.cast_ofNat, gt_iff_lt, OfNat.ofNat_ne_zero, Nat.succ_ne_self, Nat.reduceEqDiff, or_self, or_false, or_true, implies_true]
  -- $x = 6$.
  simp only [Nat.cast_ofNat, gt_iff_lt, OfNat.ofNat_ne_zero, Nat.succ_ne_self, Nat.reduceEqDiff, or_self, or_false, or_true, implies_true]
  -- $x = 7$.
  simp only [Nat.cast_ofNat, gt_iff_lt, OfNat.ofNat_ne_zero, Nat.reduceEqDiff, Nat.succ_ne_self, or_self, imp_false, not_lt, ge_iff_le]
  rw [hf]
  ring_nf
  linarith
  -- $x = 8$.
  simp only [Nat.cast_ofNat, gt_iff_lt, OfNat.ofNat_ne_zero, Nat.reduceEqDiff, or_true, implies_true]
  -- If $x = 0, 3, 4, 5, 6, 8$, then $h(x) > x$.
  intro heq
  rcases heq with heq | heq | heq | heq | heq | heq
  -- $x = 0,3,4,5,6,8$.
  any_goals
    rw [heq, hf]
    ring_nf
    linarith
  -- $0 + 3 + 4 + 5 + 6 + 8 = 26$.
  norm_num
  