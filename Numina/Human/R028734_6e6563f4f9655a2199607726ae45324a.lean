import Mathlib

/- 10. $a_{1}, a_{2}, a_{3}, a_{4}$ are real numbers greater than 1, prove:

$$

8\left(a_{1} a_{2} a_{3} a_{4}+1\right) \geqslant\left(1+a_{1}\right)\left(1+a_{2}\right)\left(1+a_{3}\right)\left(1+a_{4}\right) .

$$
 -/
theorem inequalities_108911 (a : Fin 4 → ℝ) (ha : ∀ i, 1 < a i) :
    8 * (a 0 * a 1 * a 2 * a 3 + 1) ≥ (1 + a 0) * (1 + a 1) * (1 + a 2) * (1 + a 3) := by
  -- first prove a lemma that 1 < a, b implies 2(ab+1) ≥ (1+a)*(1+b)
  have aux {a b : ℝ} (ha: 1 < a) (hb: 1 < b) : 2 * (a * b + 1) ≥ (1 + a) * (1 + b) := by
    nlinarith
  -- we'll prove the result for generalized version, 2^(n-1) * ((product of a_i) + 1) ≥ product of (a_i + 1) for 2 ≤ n
  have gen {n : ℕ} (hn : 2 ≤ n) {a : Fin n → ℝ} (ha : ∀ i, 1 < a i) : 2^(n-1) * ((∏ i, a i) + 1) ≥ ∏ i, (a i + 1) := by
    -- use induction
    induction' n, hn using Nat.le_induction with m hm hm'
      -- for n = 2, we use the lemma
    . simp
      linear_combination aux (ha 0) (ha 1)
      -- for m + 1, first define sequence b to be the first m values of a
    . let b := fun (i : Fin m) ↦ a i
      calc
      -- first rewrite the 2's power
      2 ^ (m + 1 - 1) * (∏ i : Fin (m + 1), a i + 1) = 2^(m-1) * 2 * (∏ i : Fin (m + 1), a i + 1) := by
        suffices (2: ℝ) ^(m+1-1) = 2^(m-1) * 2 by rw [this]
        rw [← pow_succ]
        congr
        omega
      -- break the product to b's and a_m
      _ = 2^(m-1) * 2 * ((∏ i , b i) * a m + 1) := by
        congr
        rw [Fin.prod_univ_castSucc]
        simp
        left
        apply Finset.prod_congr rfl
        rintro i hi
        simp [b]
      -- use the lemma on the product of b and a_m
      _ ≥ 2^(m-1) * (1 + ∏ i, b i) * (1 + a m) := by
        rw [mul_assoc, mul_assoc]
        gcongr 2^(m-1) * ?_
        rw [← ge_iff_le]
        apply aux
        . rw [show (1:ℝ) = ∏ i : Fin m, 1 by exact Eq.symm (Fintype.prod_eq_one (fun a => 1) (congrFun rfl))]
          apply Finset.prod_lt_prod
          . simp
          . rintro i hi
            exact le_of_lt (ha i)
          . use ⟨0, by omega⟩
            simp [b]
            exact ha 0
        . exact ha m
      -- now use inductive hypothesis on b's
      _ ≥ (∏ i, (b i + 1)) * (1 + a m) := by
          gcongr
          . linarith [ha m]
          . rw [← ge_iff_le, add_comm]
            apply hm'
            rintro i
            exact ha i
      -- now get back to all a
      _ = ∏ i , (a i + 1) := by
        rw [Fin.prod_univ_castSucc]
        congr 1
        . apply Finset.prod_congr rfl
          rintro i hi
          simp [b]
        . simp
          ring
  -- now just apply the theorem for n = 4
  convert gen (show 2 ≤ 4 by norm_num) ha
  . ring
  . rw [Fin.prod_univ_four]
  . rw [Fin.prod_univ_four]
    ring