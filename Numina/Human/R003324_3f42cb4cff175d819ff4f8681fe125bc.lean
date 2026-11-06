import Mathlib

set_option maxRecDepth 3000

/- In a non-zero common difference arithmetic sequence $a_{1} \cdot a_{2}, \cdots, a_{1990}$, $a_{i} a,>0,(i, j=1,2, \cdots, 1990)$. Let $b_{1}=a_{1} \cdot a_{1990}, b_{2}=a_{2} \cdot a_{1989}, \cdots, b_{k}=a_{k} \cdot a_{1990-k+1}(k=1,2, \cdots, 1990)$, then the largest term in $\left\{b_{k}\right\}$ is $\qquad$ . -/

-- lemma that if a + b = c + d and |b-a| ≤ |d-c| then c * d ≤ a * b
lemma l_prod_le_prod_of_diff_le_diff (a b c d : ℝ) (h : a + b = c + d) (h' : |b - a| ≤ |d - c|) :
  c * d ≤ a * b := by
  suffices (c + d)^2 - (d - c)^2 ≤ (a + b)^2 - (b - a)^2 by linarith
  rw [h]
  suffices (b - a)^2 ≤ (d - c)^2 by linarith
  rwa [sq_le_sq]

-- lemma that integer subtraction of two naturals is 0 iff a = b, newer version of mathlib has this, so had to prove in this version.
lemma l_subNat_eq_zero_iff {a b : Nat} : Int.subNatNat a b = 0 ↔ a = b := by
  cases Nat.lt_or_ge a b with
  | inl h =>
    rw [Int.subNatNat_of_lt h]
    simpa using ne_of_lt h
  | inr h =>
    rw [Int.subNatNat_of_le h]
    norm_cast
    rw [Nat.sub_eq_iff_eq_add' h]
    simp

theorem algebra_169399 (a b : Fin 1990 → ℝ) (d : ℝ) (h₀ : ∀ i, a i = a 0 + d * i)
    (h₁ : ∀ i, b i = a i * a (1989 - i)) (x : ℝ)
    (h₃ : IsGreatest {b i | (i : Fin 1990) } x) : x = b 994 ∧ x = b 995 := by
  -- one of the hypothesis related to positiveness is illegible and also not required, so not written
  -- indices have been shifted by 1 down for ease of work
  -- first prove b(994) = b(995) so proving one (995) is enough
  have b_same : b 994 = b 995 := by
    rw [h₁, h₁]
    ring_nf
  rw [b_same]
  simp
  -- for all i, a i + a (1989 - i) = a fixed value
  have a_sum (i : Fin 1990) : a i + a (1989 - i) = 2 * a 0 + d * 1989 := by
    rw [h₀ i, h₀ (1989 - i)]
    suffices d * i + d * ↑(1989 - i) = d * 1989 by linarith
    rw [← mul_add]
    congr
    norm_cast
    rw [Fin.sub_val_of_le]
    . rw [show ↑(1989 : Fin 1990) = (1989 : ℕ) by norm_cast]
      omega
    . rw [Fin.le_def]
      rw [show ↑(1989 : Fin 1990) = (1989 : ℕ) by norm_cast]
      omega
  -- we'll prove x ≤ b 995 ≤ x
  apply le_antisymm
  -- to prove x ≤ b 995, x must be some b i, so we'll prove b i ≤ b 995
  . have := h₃.left
    simp at this
    obtain ⟨i, hx⟩ := this
    rw [← hx]
    rw [h₁, h₁]
    -- by lemma proving inequality of differences is enough, as sums are conntant
    apply l_prod_le_prod_of_diff_le_diff
    . rw [a_sum, a_sum]
    . ring_nf
      rw [h₀ 994, h₀ 995, h₀ i, h₀ (1989 - i)]
      ring_nf
      -- we have to prove following where lhs is just |d|
      convert_to |d * 994 - d * 995| ≤ |d * (↑↑(1989 - i) - ↑↑i)|
      . congr
        rw [mul_sub]
      conv_lhs => ring_nf
      rw [abs_neg, abs_mul]
      -- we'll prove the multiplicant at rhs is >= 1
      suffices 1 ≤ |(↑(1989 - i) - i : ℝ)| by
        apply le_mul_of_one_le_right
        . simp
        . assumption
      -- first convert to integers , then the inequality is proved if we can prove the subtraction is never 0
      norm_cast
      rw [le_abs]
      suffices  Int.subNatNat ↑(1989 - i) ↑i ≠ 0 by omega
      -- if subtraction is 0 then by lemma, the values are equal
      by_contra h
      rw [l_subNat_eq_zero_iff] at h
      -- i.e. equal as natural numbers, but that is not possible
      have := Fin.eq_of_val_eq h
      omega
  -- proving b 995 ≤ x is easy as b 995 is in the set and x is upper bound
  . have := h₃.right
    simp [upperBounds] at this
    specialize this 995
    assumption