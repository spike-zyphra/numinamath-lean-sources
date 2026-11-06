import Mathlib

/- Point $C$ is the midpoint of $\overline{AB}$, point $D$ is the midpoint of $\overline{AC}$, point $E$ is the midpoint of $\overline{AD}$, and point $F$ is the midpoint of $\overline{AE}$. If $AF=3$, what is the number of units in the length of $\overline{AB}$?-/
open EuclideanGeometry
open Real

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

theorem algebra_14358 {A B C D E F : P}  (hC : C = midpoint ℝ  A B)
    (hD : D = midpoint ℝ  A C) (hE : E = midpoint ℝ  A D) (hF : F = midpoint ℝ  A E)
    (hF' :dist A F = 3) : dist A B= 48 := by
    --Drawing a figure allows us to see that $3=AF=\frac{AE}{2}=\frac{AD}{4}=\frac{AC}{8}=\frac{AB}{16}\implies AB=\boxed{48}$.
    --[asy]pair A,B,C,D,E,F;A = (0,0);B = (1,0);C = B/2;D=C/2;E = D/2;F=E/2;draw(A--B);dot(A);dot(B);dot(C);dot(D);dot(E);dot(F);label("$A$",A,S);label("$B$",B,S);label("$C$",C,S);label("$D$",D,S);label("$E$",E,S);label("$F$",F,S);[/asy]
    rw [hF] at hF'
    rw [midpoint,dist_comm,dist_lineMap_left,invOf_eq_inv,norm_inv] at hF'; norm_num at hF';
    rw [hE] at hF'
    rw [midpoint,dist_comm,dist_lineMap_left,invOf_eq_inv,norm_inv] at hF'; norm_num at hF';
    rw [hD] at hF'
    rw [midpoint,dist_comm,dist_lineMap_left,invOf_eq_inv,norm_inv] at hF'; norm_num at hF';
    rw [hC] at hF'
    rw [midpoint,dist_comm,dist_lineMap_left,invOf_eq_inv,norm_inv] at hF'; norm_num at hF';
    ring_nf at hF'
    have heq :=  congrArg ( fun (t) => (t) * 16 ) hF'; simp at heq; ring_nf at heq
    exact heq
