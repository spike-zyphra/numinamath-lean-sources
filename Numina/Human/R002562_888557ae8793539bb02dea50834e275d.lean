import Mathlib

open Real

/- Let $S$ be the set of positive integers $n$ for which $\tfrac{1}{n}$ has the repeating decimal representation $0.\overline{ab} = 0.ababab\cdots,$ with $a$ and $b$ different digits.  What is the sum of the elements of $S$?
$\textbf{(A)}\ 11\qquad\textbf{(B)}\ 44\qquad\textbf{(C)}\ 110\qquad\textbf{(D)}\ 143\qquad\textbf{(E)}\ 155\qquad$ -/
theorem number_theory_95482 :
    ∑ᶠ n ∈ {n : ℕ | 0 < n ∧ ∃ a b : ℕ, a ≠ b ∧ a ≤ 9 ∧ b ≤ 9 ∧ (1 / n : ℚ) = (a * 10 + b : ℚ) / 99 ∧ n ≠ 1}, n = 143 := by
  have ce : {n : ℕ | 0 < n ∧ ∃ a b : ℕ, a ≠ b ∧ a ≤ 9 ∧ b ≤ 9 ∧ (1 / n : ℚ) = (a * 10 + b : ℚ) / 99 ∧ n ≠ 1} = ↑({11, 33, 99} : Finset ℕ) := by
    symm
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      ne_eq, Set.mem_setOf_eq]
    constructor <;> intro h
    · obtain rfl | rfl | rfl := h
      all_goals norm_num
      -- supply 3 witnesses
      exists 0, 9; norm_num
      exists 0, 3; norm_num
      exists 0, 1; norm_num
    · obtain ⟨h1, ⟨a, b, c, d, e, f, g⟩⟩ := h
      simp only [one_div] at f
      apply_fun (fun x => x⁻¹) at f
      simp only [inv_inv, inv_div] at f
      -- prepare for divisibility constraint
      have de : x * (a * 10 + b) = 99 := by
        qify
        by_cases nz : a * 10 + b = 0
        · qify at nz
          rw [nz] at f; norm_num at f
          rw [f] at h1; norm_num at h1
        qify at nz
        apply_fun (fun x => x * (↑a * 10 + ↑b)) at f
        conv at f => right; simp only [isUnit_iff_ne_zero, ne_eq, nz, not_false_eq_true,
          IsUnit.div_mul_cancel]
        exact f
      -- divisibility constraint
      have dv : a * 10 + b ∣ 99 := by exact Dvd.intro_left x de
      -- remove any mention of x
      qify
      rw [f]
      qify at h1 g
      rw [f] at h1 g

      clear f de x
      -- turn into fin
      obtain ⟨wa, ha⟩ : ∃ wa : Fin 10, wa.1 = a := ⟨⟨a, by linarith⟩, by norm_cast⟩
      obtain ⟨wb, hb⟩ : ∃ wb : Fin 10, wb.1 = b := ⟨⟨b, by linarith⟩, by norm_cast⟩
      subst a b
      revert wa wb d e c h1 g dv
      -- we end up with the 3 elements
      native_decide
  -- sum everything
  rw [ce, finsum_mem_coe_finset]
  native_decide