/-
Let $f(x)=\frac{1}{1-x}$. Let $f^{k+1}(x)=f\left(f^{k}(x)\right)$, with $f^{1}(x)=f(x)$. What is $f^{2008}(2008)$ ?
-/
theorem hmit (f : ℝ → ℝ) (fdef : ∀ x, f x = (1 : ℝ) / ((1 : ℝ) - x)) :
    f^[2008] 2008 = -1 / 2007 := by
  have iter2 : ∀ x, x ≠ 0 ∧ x ≠ 1 → f^[2] x = (x - 1) / x := fun x ⟨hx0, hx1⟩ => by
    simp only [Function.iterate_succ, Function.iterate_one, Function.comp_apply, 
      Function.iterate_zero_apply, fdef x, fdef (1 / (1 - x))] 
    conv_lhs => enter [2, 1]; rw [← div_self (a := 1 - x) (sub_ne_zero_of_ne (Ne.symm hx1))]
    rw [div_sub_div_same, one_div_div]
    ring 

  have iter3 : ∀ x, x ≠ 0 ∧ x ≠ 1 → f^[3] x = x := fun x ⟨hx0, hx1⟩ => by
    rw [Function.iterate_succ', Function.comp_apply, iter2 x ⟨hx0, hx1⟩, fdef]
    field_simp

  have iter3k : ∀ (k : ℕ) (x : ℝ), x ≠ 0 ∧ x ≠ 1 → f^[3 * k] x = x := fun k x ⟨hx0, hx1⟩ ↦ by
    induction k with
    | zero => simp
    | succ n h => 
      rw [mul_add, mul_one, Function.iterate_add, Function.comp_apply, iter3 x ⟨hx0, hx1⟩, h]

  rw [Function.iterate_succ', Function.comp_apply, show 2007 = 3 * 669 by ring, 
    iter3k 669 2008 ⟨by norm_num, by norm_num⟩, fdef]
  ring