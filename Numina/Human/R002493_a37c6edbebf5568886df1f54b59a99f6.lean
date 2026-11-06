import Mathlib
open Real
/- log p + log q = log (p+q) only if
(A) p=q=0 (B) p=q^2/(1-q) (C) p=q=1 (D) p=q/(q-1) (E) p=q/(q+1) -/
theorem algebra_94214 {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hq' : q-1 ≠ 0)
(h : log p + log q = log (p + q)) :
p = q / (q - 1) := by
-- using the formula log p + log q = log (p * q) to simplify the equation
  rw [← log_mul (ne_of_gt hp) (ne_of_gt hq)] at h
-- using the injective property to get rid of the logarithm
  have h':p*q=p+q:=log_injOn_pos (by simp [hp,hq]) (by simp;linarith) h
-- unifying the equations obtained just now and the goal
  field_simp
  linarith