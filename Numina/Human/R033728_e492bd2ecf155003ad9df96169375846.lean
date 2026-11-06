import Mathlib

/-If $f(x)=5x-12$, find a value for $x$ so that $f^{-1}(x)=f(x+1)$.-/
theorem algebra_21499 {f : ℝ → ℝ} (x : ℝ) (hf : f = fun x => 5 * x - 12) (hx : f ⁻¹' {x} = {f (x + 1)}) : x = 47 / 24 := by
  rw [hf] at hx
  simp [Set.preimage] at hx
  -- show that {x_1 | 5 * x_1 - 12 = x} = {x_1 | x_1 = (x + 12) / 5}
  have set_eq : {x_1 | 5 * x_1 - 12 = x} = {x_1 | x_1 = (x + 12) / 5} := by
    ext y
    simp
    ring_nf
    -- divide into two parts
    apply Iff.intro <;> intro h
    all_goals linarith only [h]
  -- show that (x + 12) / 5 = 5 * (x + 1) - 12
  rw [set_eq] at hx
  clear set_eq
  rw [Set.set_compr_eq_eq_singleton, Set.singleton_eq_singleton_iff] at hx
  -- finally get the answer of x
  linarith only [hx] 