import Mathlib

open Polynomial

/- Let $P$ be a polynomial with integer coefficients. Suppose that for $n=1,2,3, \ldots, 1998$ the number $P(n)$ is a three-digit positive integer. Prove that the polynomial $P$ has no integer roots.-/
theorem algebra_241112 {p : ℤ[X]} (hp : ∀ n ∈ Set.Icc 1 1998, p.eval n ∈ Set.Icc 100 999) :
    p.roots = ∅ := by
  -- Let $m$ be an arbitrary integer
  ext m
  -- and define $n \in\{1,2, \ldots, 1998\}$ to be such that $m \equiv n(\bmod 1998)$.
  let n := (m - 1) % 1998 + 1
  -- Then $P(m) \equiv P(n)(\bmod 1998)$.
  have modeq : p.eval m ≡ p.eval n [ZMOD 1998] := by
    rw [← sum_C_mul_X_pow_eq p, eval_sum, eval_sum, Int.ModEq, sum, sum]
    conv => congr; rw [Finset.sum_int_mod]; rfl; rw [Finset.sum_int_mod]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [eq_intCast, eval_mul, eval_intCast, Int.cast_id, eval_pow, eval_X]
    change _ ≡ _ [ZMOD 1998]
    gcongr
    symm
    calc
      _ ≡ (m - 1) % 1998 + 1 [ZMOD 1998] := by congr
      _ ≡ (m - 1) + 1 [ZMOD 1998] := by gcongr; rw [Int.ModEq, Int.emod_emod]
      _ ≡ _ [ZMOD 1998] := by congr; omega
  simp only [count_roots, Multiset.empty_eq_zero, Multiset.not_mem_zero, not_false_eq_true,
    Multiset.count_eq_zero_of_not_mem, rootMultiplicity_eq_zero_iff, IsRoot.def]
  rw [imp_iff_not_or]
  left
  intro hp0
  -- Since $P(n)$ as a three-digit number cannot be divisible by 1998 ,
  have mod1998_of_mem {n : ℤ} (hn : n ∈ Set.Icc 1 1998) : ¬p.eval n ≡ 0 [ZMOD 1998] := by
    intro h
    specialize hp _ hn
    simp at hp
    rw [Int.ModEq, Int.emod_eq_of_lt (by omega) (by omega)] at h
    simp [h] at hp
  -- then $P(m)$ cannot be equal to 0 . Hence $P$ has no integer roots.
  have mod1998 : p.eval m ≡ 0 [ZMOD 1998] := by norm_num [hp0]
  have nmem : n ∈ Set.Icc 1 1998 := by simp; omega
  absurd mod1998_of_mem nmem
  exact Int.ModEq.trans modeq.symm mod1998
