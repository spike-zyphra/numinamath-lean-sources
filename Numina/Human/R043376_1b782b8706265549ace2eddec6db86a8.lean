import Mathlib

open Real

/- Solve the equation


$$

\frac{1}{\log _{\frac{1}{2}} x}+\frac{1}{\log _{\frac{2}{3}} x}+\cdots+\frac{1}{\log _{\frac{9}{10}} x}=1

$$


on the set of real numbers. ()

Mathematics Competition of Secondary Schools in Hajdú-Bihar County 2002/2003 -/
theorem algebra_208286 (x : ℝ) (hx : 0 < x) :
    ∑ i ∈ Finset.range 9, (1 / logb ((i + 1) / (i + 2)) x) = 1 ↔ x = 1 / 10 := by

  repeat rw [Finset.sum_range_succ]
  simp
  -- we'll need a lemma for Real.logb (a/b) c
  have hlogb : ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → logb (a / b) c = logb 10 c / (logb 10 a - logb 10 b) := by
    intros a b c ha hb hc
    rw [logb_div_base (by linarith) (by linarith), inv_logb, inv_logb, ← div_logb (c:=10) (by norm_num) (by norm_num) (by norm_num), ← div_logb (a:=c) (b:=b) (c:=10) (by norm_num) (by norm_num) (by norm_num),
        ← inv_logb, ← inv_logb 10 a, ← inv_logb 10 b]; field_simp
    calc _
    _ = 1 / ((logb 10 a - logb 10 b) / logb 10 c) := by ring_nf
    _ = logb 10 c / (logb 10 a - logb 10 b) := by rw [div_eq_inv_mul, div_eq_inv_mul]; simp; ring_nf;
  -- left implication is simple
  constructor
  rotate_left
  · intro hx'; rw [hx']
    norm_num
    repeat rw [hlogb _ _ _ (by norm_num) (by norm_num) (by norm_num)]
    simp
    ring_nf
  -- right implication telescopes
  intro h
  norm_num at h
  repeat rw [hlogb _ _ _ (by norm_num) (by norm_num) hx] at h
  simp at h
  ring_nf at h
  -- now a simple equation to solve
  apply congr_arg (fun x=>(-x)⁻¹) at h
  simp at h; ring_nf at h
  rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hx] at h
  ring_nf at h ⊢
  exact h.symm