import Mathlib
/-Tracy had a bag of candies, and none of the candies could be broken into pieces. She ate $\frac{1}{3}$ of them and then gave $\frac{1}{4}$ of what remained to her friend Rachel. Tracy and her mom then each ate 15 candies from what Tracy had left. Finally, Tracy's brother took somewhere from one to five candies, leaving Tracy with three candies. How many candies did Tracy have at the start? -/

theorem algebra_15792 {x : ℕ} (hx : 2 ∣ x ∧ 3 ∣ x ∧ 6 ∣ x)
    (h : (x / 3) + (2 / 3 * (1 / 4) * x) + (15:ℚ) + 15 + 1 + 3 ≤ x ∧ x ≤ (x / 3) + (2 / 3 * (1 / 4) * x) +(15:ℚ) + 15 + 5 + 3) :
    x = 72 := by
    ring_nf at h
    rcases hx with ⟨hx1, ⟨hx2, hx3⟩⟩
    --Let $x$ be Tracy's starting number of candies. After eating $\frac{1}{3}$ of them, she had $\frac{2}{3}x$ left. Since $\frac{2}{3}x$ is an integer, $x$ is divisible by 3. After giving $\frac{1}{4}$ of this to Rachel, she had $\frac{3}{4}$ of $\frac{2}{3}x$ left, for a total of $\frac{3}{4} \cdot \frac{2}{3}x = \frac{1}{2}x$. Since $\frac{1}{2}x$ is an integer, $x$ is divisible by 2. Since $x$ is divisible by both 2 and 3, it is divisible by 6.
    rcases h with ⟨hl, hr⟩
    apply le_sub_right_of_add_le at hl; ring_nf at hl
    rw [← tsub_le_iff_right] at hr; ring_nf at hr
    have h2 :  0 ≤ (2 : ℚ)  := by simp
    have hl2 := mul_le_mul_of_nonneg_right hl h2; simp at hl2; ring_nf at hl2
    have hr2 := mul_le_mul_of_nonneg_right hr h2; simp at hr2; ring_nf at hr2
    norm_cast at hl2; norm_cast at hr2
    have hc := exists_eq_mul_left_of_dvd hx3
    --After Tracy and her mom each ate 15 candies (they ate a total of 30), Tracy had $\frac{1}{2}x - 30$ candies left. After her brother took 1 to 5 candies, Tracy was left with 3. This means Tracy had 4 to 8 candies before her brother took some candies. Hence, $$4 \le \frac{1}{2}x - 30 \le 8\qquad \Rightarrow \qquad 34 \le \frac{1}{2}x \le 38\qquad  \Rightarrow \qquad 68 \le x \le 76.
    cases hc with
    | intro w h =>
      rw[← Nat.lt_succ_iff] at hr2; simp at hr2
      have xx : x ∈ List.Ico 68 77 := by
        simp
        constructor
        .
          linarith
        .
          linarith
      --$$Since $x$ is divisible by 6, and the only multiple of 6 in the above range is 72, we have $x = \boxed{72}$.
      fin_cases xx
      any_goals simp; contradiction
      simp