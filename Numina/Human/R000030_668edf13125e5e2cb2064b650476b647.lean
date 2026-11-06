import Mathlib

open Real

/-- Auxiliary lemma : $1.41 < \sqrt{2}-/
@[simp]
lemma lt_sqrt2 : 1.41 < √ 2 := lt_sqrt_of_sq_lt (by norm_num)

/-- Auxiliary lemma : $\sqrt{2} < 1.42-/
@[simp]
lemma sqrt2_lt : √ 2 < 1.42 := (sqrt_lt' (by norm_num)).mpr (by norm_num)

/-- Auxiliary lemma : $\sqrt{2} < 1.415 -/
@[simp]
lemma sqrt2_ltt : √2 < 1.415 := (sqrt_lt' (by norm_num)).mpr (by norm_num)

/-- Auxiliary lemma : $1< \sqrt{2} - \frac 1 3-/
lemma ineq1 : 1 < √2 - 3⁻¹ := by
  calc
    _ < (1.41 : ℝ) - 1 / 3 := by norm_num
    _ < _ := by simp

/-- Auxiliary lemma : $\sqrt{2} + \frac 1 3 < 2-/
lemma ineq2 : √2 + 3⁻¹ < 2 :=
  calc
    _ < (1.42 : ℝ) + 1 / 3 := by simp
    _ < _ := by norm_num

/-- Auxiliary lemma : if $a-1 < b < a+1$ where $a$ and $b$ are integers, then $b =a $. -/
lemma eq_of_consecutive {a b : ℤ} (h1 : a - 1 < b) (h2 : b < a + 1) : b = a := by
  rw [Int.sub_one_lt_iff] at h1
  rw [Int.lt_add_one_iff] at h2
  linarith

/-- Auxiliary lemma : if $a < b$ where $a$ is a positive real number, then $a^2 < b^2$. -/
lemma sq_lt_sq_of_nn {a b : ℝ} (ha : 0 ≤ a) (h : a < b) : a ^ 2 < b ^ 2 :=
  sq_lt_sq' (by linarith) h

/-- Show that there is no natural number $n$ for which the interval $\left(n \sqrt{2}-\frac{1}{3 n}, n \sqrt{2}+\frac{1}{3 n}\right)$ contains an integer.-/
theorem number_theory_4058 (n : Nat) (npos : n ≠ 0): ¬ ∃ k : Int, n * (2 : Real).sqrt - 1 / (3 * n) < k ∧
  k < n * (2 : Real).sqrt + 1 / (3 * n) := by
    -- consider the natural number $n=1$. 
    by_cases hn : n = 1
    · simp_rw [hn]; intro h; simp at h
      obtain ⟨k, hk⟩ := h
      have hk' : 1 < k ∧ k < 2 := by
        have h1 := ineq1.trans hk.1
        have h2 := hk.2.trans ineq2
        norm_cast at *
      exact not_le_of_lt  hk'.2 <| Int.add_one_le_of_lt hk'.1
    · -- now consider $n \geq 2$ and assume, contrary to the problem statement, that exists an integer k such that : 
      -- $n\sqrt2 - \frac 1 {3n} < k < n\sqrt2 + \frac 1 {3n}$.
      intro h
      have two_len := (Nat.two_le_iff n).2 ⟨npos,hn⟩
      obtain ⟨k, hk⟩ := h
      have : (n : ℝ) ≠ 0 := by norm_cast
      have sqeq1 : (n * √2 - 1 / (3 * ↑n)) ^ 2 = 2 * n ^ 2 - (2 * √ 2) / 3 + 1 / (9 * n ^ 2) := by
        calc
          _ = (↑n * √2) ^ 2 - 2 * (↑n * √2) * (1 / (3 * ↑n)) + (1 / (3 * ↑n)) ^ 2 := by rw [sub_sq]
          _ = _ := by
            rw [mul_pow, div_pow]; congr 2
            · simp; ring
            · rw [mul_assoc, mul_div, mul_one, mul_comm (n : ℝ) _, mul_div_mul_right _ _ this]
              ring
            · simp
            ring
      -- Thus, the interval for $k^2$ is $( (n\sqrt2 - \frac 1 {3n})^2, (n\sqrt2 + \frac 1 {3n})^2 )$, included within the interval $(2n^2-1, 2n^2 + 1)$.
      have h1 : 2 * (n : ℝ) ^ 2 - 1 ≤ (n * √2 - 1 / (3 * n)) ^ 2 := by
        rw [sqeq1]; simp; rw [add_assoc, sub_add]; rw [le_sub_comm]; simp
        calc
          _ ≤ (1 : ℝ) := by
            apply (div_le_one (by linarith)).2
            have : 2 * √ 2 ≤ 2 * 1.42 := by simp; exact le_of_lt sqrt2_lt
            exact this.trans (by norm_num)
          _ ≤ _ := by simp
      have h2 : (n * √2 + 1 / (3 * ↑n)) ^ 2 < 2 * n ^ 2 + 1 := by
        rw [add_sq, mul_pow, div_pow, add_assoc]
        simp only [Nat.ofNat_nonneg, sq_sqrt, mul_inv_rev,one_pow]
        nth_rw 1 [mul_comm]
        refine add_lt_add_left ?_ (2 * (n : ℝ) ^ 2)
        rw [mul_assoc, mul_div, mul_one]
        nth_rw 3 [mul_comm]; rw [mul_div_mul_left _ _ this]
        have h3 : 1 / (3 * (n : ℝ)) ^ 2 ≤ 1 / 18 := by
          rw [mul_pow, div_le_div_iff (by positivity) (by linarith)]; norm_num
          rw [show ((18 : ℝ) = 9 * 2 ) by norm_num, mul_le_mul_left (by positivity)]
          have : (2 :ℝ) ≤ n := by norm_cast
          have : (2 : ℝ) ^ 2 ≤ n ^ 2 := pow_le_pow_left (by linarith) this 2
          exact le_trans (by norm_num) this
        exact lt_of_le_of_lt (add_le_add_left h3 (2 * (√2 / 3))) (by
            calc
              _ < 2 * ((1.415 : ℝ) / 3) + 1 / 18 := by
                refine add_lt_add_right ?_ (1 / 18)
                simp; refine div_lt_div_of_pos_right sqrt2_ltt (by simp)
              _ < _ := by norm_num
          )
      have le1 : 0 ≤ n * √2 - 1 / (3 * n) := by
        calc
          _ ≤ √2 - 1 / 3 := by norm_num; exact le_trans (by norm_num) (le_of_lt lt_sqrt2)
          _ ≤ _ := by
            apply sub_le_sub
            · simp; exact le_trans (by linarith) ((Nat.two_le_iff n).2 ⟨npos, hn⟩)
            · norm_num; exact Nat.cast_inv_le_one n
      have hk' : (n * √2 - 1 / (3 * ↑n)) ^ 2 < (k ) ^ 2 ∧ k ^ 2 < (n * √2 + 1 / (3 * ↑n)) ^ 2 :=
        ⟨sq_lt_sq_of_nn le1 (by linarith), sq_lt_sq_of_nn (by linarith) hk.2⟩
      have hkk : 2 * n ^ 2 - 1 < k ^ 2 ∧ k ^ 2 < 2 * n ^ 2 + 1 :=
        ⟨by convert lt_of_le_of_lt h1 hk'.1 using 2; norm_cast,
          by convert lt_trans hk'.2 h2; norm_cast⟩
      have h3 : k ^ 2 = 2 * n ^ 2 := eq_of_consecutive hkk.1 hkk.2
      have h4 : k / n  = √ 2 := by
        rw [div_eq_iff this, ←sq_eq_sq, mul_pow]; norm_num
        convert h3; norm_cast
        · have : 0 < ↑n * √2 - 1 / (3 * ↑n) := by
            calc
              _ < √2 - 1 := by simp; exact lt_trans (by norm_num) lt_sqrt2
              _ < _ := by
                apply sub_lt_sub
                · simp; linarith
                · rw [one_div_lt (by positivity) (by positivity)]; simp; norm_cast; linarith
          linarith
        · linarith
      have h5 := (irrational_iff_ne_rational √2).not.2
      push_neg at h5
      replace h5 := h5 ⟨k , n, h4.symm ⟩
      exact h5 irrational_sqrt_two
