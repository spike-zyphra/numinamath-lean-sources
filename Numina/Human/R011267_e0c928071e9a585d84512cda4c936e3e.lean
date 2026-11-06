import Mathlib

open Finset

/-8. Let the equation $x y z=900$ have all positive integer solutions $\left(x_{i}, y_{i}, z_{i}\right)(1 \leqslant i \leqslant n)$. Then $\sum_{k=1}^{n}\left(x_{k}+y_{k}+z_{k}\right)=$-/
theorem number_theory_106801 : ∑ᶠ x ∈ {(x, y, z) : ℕ×ℕ×ℕ | x * y * z = 900}, (x.1 + x.2.1 + x.2.2) = 22572 := by
  set S := (Finset.sup (Nat.divisorsAntidiagonal 900) (fun (x, y) => Finset.map { toFun := Prod.mk x, inj' := Prod.mk.inj_left x } (Nat.divisorsAntidiagonal y)) : Finset (ℕ×ℕ×ℕ)) with hS
  have h₁ : {(x, y, z) : ℕ×ℕ×ℕ | x * y * z = 900} = S := by
    rw [hS]
    ext ⟨a, b, c⟩
    simp only [Set.mem_setOf_eq, mem_coe, mem_sup, Nat.mem_divisorsAntidiagonal, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, and_true, mem_map, Function.Embedding.coeFn_mk,
      Prod.mk.injEq, exists_eq_right_right, Prod.exists]
    constructor
    · intro h
      use a, b * c
      simp only [mul_eq_zero, not_or, true_and, and_true]
      split_ands
      · rw [←mul_assoc]
        exact h
      all_goals
      · intro h'
        rw [h'] at h
        norm_num at h
    · simp only [forall_exists_index, and_imp]
      intro x y hxy hxy' hy hx
      rw [hxy'.symm, hx, ←mul_assoc] at hxy
      exact hxy
  rw [h₁, finsum_mem_coe_finset, hS]
  native_decide
