import Mathlib

open Finset Real Polynomial

/- Let $n$ be an integer greater than 1 , and let $a_{0}, a_{1}, \ldots, a_{n}$ be real numbers with $a_{1}=a_{n-1}=0$. Prove that for any real number $k$,

$$
\left|a_{0}\right|-\left|a_{n}\right| \leq \sum_{i=0}^{n-2}\left|a_{i}-k a_{i+1}-a_{i+2}\right|
$$ -/
theorem inequalities_606006 {n : ℕ} (hn : 1 < n) (a : ℕ → ℝ)
    (h₀ : a 1 = 0) (h₁ : a (n - 1) = 0) :
    ∀ k : ℝ, |a 0| - |a n| ≤ ∑ i ∈ range (n - 1), |a i - k * a (i + 1) - a (i + 2)| := by

  -- wlog assume that n > 2
  have hn : 2 ≤ n := by exact hn
  rcases lt_or_eq_of_le hn with hn | hn
  on_goal 2 =>
    simp [←hn, h₀]
    trans |a 0 - a 2 + a 2|
    · simp only [sub_add_cancel, le_refl]
    · exact abs_add_le (a 0 - a 2) (a 2)

  intro k
  -- Let $Q(x)=x^{2}-k x-1$ and let $P(x)=a_{0}+a_{1} x+\cdots+a_{n} x^{n}$.
  let Q (x : ℂ) := x ^ 2 - k * x - 1
  let P (x : ℂ) := ∑ i ∈ range (n + 1), a i * x ^ i
  -- Note that the product of the two roots of $Q(x)$ is -1
  -- and thus one of the two roots has magnitude at most 1.
  -- Let $z$ be this root.
  obtain ⟨z, hQz, hnorm⟩ : ∃ z : ℂ, Q z = 0 ∧ ‖z‖ ≤ 1 := by
    let Q' : ℂ[X] := X ^ 2 - C (k : ℂ) * X - 1
    have Q'_apply {z : ℂ} : Q'.eval z = Q z := by
      unfold Q'
      simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_one]
    have hQ' : 0 < degree Q' := by
      unfold Q'
      rw [degree_sub_eq_left_of_degree_lt]
      · rw [degree_sub_eq_left_of_degree_lt]
        · simp only [degree_pow, degree_X, nsmul_eq_mul, Nat.cast_ofNat, mul_one, Nat.ofNat_pos]
        · simp only [degree_mul, degree_X, degree_pow, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
          apply lt_of_le_of_lt (b := 0 + 1)
          · gcongr
            exact degree_C_le
          · norm_num
      · simp only [degree_one]
        rw [degree_sub_eq_left_of_degree_lt]
        · simp only [degree_pow, degree_X, nsmul_eq_mul, Nat.cast_ofNat, mul_one, Nat.ofNat_pos]
        · simp only [degree_mul, degree_X, degree_pow, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
          apply lt_of_le_of_lt (b := 0 + 1)
          · gcongr
            exact degree_C_le
          · norm_num
    have apply_eq_zero_of_isRoot {z : ℂ} (h : IsRoot Q' z) : Q z = 0 := by
      rw [←Q'_apply]
      exact h
    obtain ⟨z, hz⟩ := Complex.exists_root hQ'
    by_cases hz' : ‖z‖ ≤ 1
    · use z, apply_eq_zero_of_isRoot hz, hz'
    · have : z * z - k * z + -1 = 0 := by
        rw [←apply_eq_zero_of_isRoot hz]
        unfold Q
        ring
      obtain ⟨y, hroot, _, hmul⟩ := vieta_formula_quadratic this
      use y
      constructor
      · unfold Q
        rw [←hroot]
        ring
      · push_neg at hz'
        apply congrArg (fun x => ‖x‖) at hmul
        rw [norm_mul, norm_neg, norm_one] at hmul
        rw [←hmul]
        apply le_of_lt
        apply lt_mul_left ?_ hz'
        by_contra h
        simp only [Complex.norm_eq_abs, AbsoluteValue.pos_iff] at h
        push_neg at h
        rw [h] at hroot
        norm_num at hroot
  -- Now note that since $a_{1}=a_{n-1}=0$, we have that
  -- $$ \begin{aligned} 0=Q(z) P(z) & =-a_{0}-k a_{0} z+\sum_{i=0}^{n-2}\left(a_{i}-k a_{i+1}-a_{i+2}\right) z^{i+2}-k a_{n} z^{n+1}+a_{n} z^{n+2} \
  -- & =a_{0}(-1-k z)+\sum_{i=0}^{n-2}\left(a_{i}-k a_{i+1}-a_{i+2}\right) z^{i+2}+a_{n} z^{n}\left(z^{2}-k z\right) \ &
  -- =-a_{0} z^{2}+\sum_{i=0}^{n-2}\left(a_{i}-k a_{i+1}-a_{i+2}\right) z^{i+2}+a_{n} z^{n} \end{aligned} $$
  have hmul : 0 = -a 0 * z ^ 2 + ∑ i ∈ range (n - 1), (a i - k * a (i + 1) - a (i + 2)) * z ^ (i + 2) + a n * z ^ n := by
    trans Q z * P z
    · rw [hQz, zero_mul]
    unfold Q P
    have hn' : n + 1 = n - 1 + 2 := by simp; rw [Nat.sub_add_cancel]; exact Nat.one_le_of_lt hn
    nth_rw 1 [hn']
    rw [sub_mul, sub_mul, one_mul, mul_sum, mul_sum]
    rw [sum_range_succ, sum_range_succ]
    rw [sum_range_succ, sum_range_succ']
    rw [sum_range_succ', sum_range_succ']
    rw [zero_add, h₀, h₁, Complex.ofReal_zero, zero_mul, zero_mul, mul_zero, add_zero, add_zero, pow_zero, mul_one, Nat.sub_add_cancel (Nat.one_le_of_lt hn)]
    trans ∑ x ∈ range (n - 1), ↑(a x) * z ^ (x + 2) + ↑(a n) * z ^ (n + 2) - (∑ x ∈ range (n - 1), ↑k * ↑(a (x + 1)) * z ^ (x + 2) + k * (a 0) * z + ↑k * ↑(a n) * z ^ (n + 1)) - (∑ x ∈ range (n - 1), ↑(a (x + 2)) * z ^ (x + 2) + a 0)
    · congr 2
      · congr 1
        · congr
          ext i
          ring
        · ring
      · congr 1
        · congr 1
          · congr
            ext i
            ring
          · ring
        · ring
    trans - a 0 - k * a 0 * z + ∑ i ∈ range (n - 1), (a i * z ^ (i + 2) - k * a (i + 1) * z ^ (i + 2) - a (i + 2) * z ^ (i + 2)) - k * a n * z ^ (n + 1) + a n * z ^ (n + 2)
    · rw [sum_sub_distrib, sum_sub_distrib]
      ring
    trans -↑(a 0) * (1 + k * z) + ∑ i ∈ range (n - 1), (↑(a i) * z ^ (i + 2) - ↑k * ↑(a (i + 1)) * z ^ (i + 2) - ↑(a (i + 2)) * z ^ (i + 2)) + (a n) * z ^ n * (z ^ 2 - k * z)
    · ring
    congr 1
    · congr
      · unfold Q at hQz
        apply eq_add_of_sub_eq at hQz
        apply eq_add_of_sub_eq at hQz
        rw [hQz]
        ring
      · ext i
        ring
    · have : z ^ 2 - ↑k * z = 1 := by
        unfold Q at hQz
        apply eq_add_of_sub_eq at hQz
        rw [hQz]
        ring
      simp [this]
  -- where the third equality follows since $z^{2}-k z-1=0$.
  -- The triangle inequality now implies
  -- $$ \begin{aligned} \left|a_{0}\right| \cdot|z|^{2}
  -- & \leq\left|a_{n}\right| \cdot|z|^{n}+\sum_{i=0}^{n-2}\left|a_{i}-k a_{i+1}-a_{i+2}\right| \cdot|z|^{i+2}
  -- \ & \leq\left|a_{n}\right| \cdot|z|^{2}+\sum_{i=0}^{n-2}\left|a_{i}-k a_{i+1}-a_{i+2}\right| \cdot|z|^{2} \end{aligned} $$
  have hle : |a 0| * ‖z‖ ^ 2 ≤ ∑ i ∈ range (n - 1), |a i - k * a (i + 1) - a (i + 2)| * ‖z‖ ^ (i + 2) + |a n| * ‖z‖ ^ n := by
    trans ‖a 0 * z ^ 2 + 0‖
    · simp only [add_zero, norm_mul, Complex.norm_real, norm_eq_abs, norm_pow, le_refl]
    · rw [hmul, ←add_assoc, ←add_assoc, ←add_mul, add_neg_cancel, zero_mul, zero_add]
      trans ‖∑ i ∈ range (n - 1), (↑(a i) - ↑k * ↑(a (i + 1)) - ↑(a (i + 2))) * z ^ (i + 2)‖ + ‖↑(a n) * z ^ n‖
      · apply norm_add_le
      · gcongr
        · trans ∑ i ∈ range (n - 1), ‖(↑(a i) - ↑k * ↑(a (i + 1)) - ↑(a (i + 2))) * z ^ (i + 2)‖
          · apply norm_sum_le
          · gcongr
            rw [norm_mul]
            gcongr
            · norm_cast
            · simp only [norm_pow, Complex.norm_eq_abs, le_refl]
        · rw [norm_mul]
          gcongr
          all_goals simp
  -- since $|z| \leq 1$ and $n \geq 2$.
  -- Since $z \neq 0$, the inequality is obtained on dividing by $|z|^{2}$.
  have hzpos : 0 < ‖z‖ := by
    by_contra h
    simp only [Complex.norm_eq_abs, AbsoluteValue.pos_iff] at h
    push_neg at h
    rw [h] at hQz
    unfold Q at hQz
    norm_num at hQz
  have hzne : ‖z‖ ^ 2 > 0 := by apply sq_pos_of_pos hzpos
  apply le_of_mul_le_mul_of_pos_right ?_ hzne
  rw [sub_mul]
  apply sub_left_le_of_le_add
  apply le_trans hle
  rw [add_comm]
  rcases lt_or_eq_of_le hnorm with h | h
  · apply add_le_add
    · apply mul_le_mul_of_nonneg_left
      · apply le_of_lt
        exact pow_right_strictAnti₀ hzpos h hn
      · exact abs_nonneg (a n)
    · rw [sum_mul]
      apply sum_le_sum
      intro i _
      by_cases hi : i = 0
      · rw [hi]
      · push_neg at hi
        apply mul_le_mul_of_nonneg_left
        · apply le_of_lt
          apply pow_right_strictAnti₀ hzpos h
          exact Nat.sub_ne_zero_iff_lt.mp hi
        · exact abs_nonneg (a i - k * a (i + 1) - a (i + 2))
  · rw [h]
    simp only [one_pow, mul_one, le_refl]
