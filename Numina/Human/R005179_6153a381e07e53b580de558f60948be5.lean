import Mathlib

open Real

/-By induction we prove the following assertion:
$$ a_{m+2 k} \leq a_{m+2 k-1}=a_{m+1} \text { holds for every k-/
lemma antitone_of_lt {a : ℕ → ℕ} (ha_mono : ∀ n, a n ≤ a (n + 2)) (ha_le : ∀ n, a (n + 2) ^ 2 ≤ (a n : ℝ) ^ 2 + 2 * a (n + 1)) (m : ℕ) (hm : a (m + 2) > a m) : ∀ k, a (m + 2 + 2 * k) ≤ a (m + 1) ∧ a (m + 1 + 2 * k) = a (m + 1) := by
  intro k
  induction k with
  | zero =>
    -- The truth of $(\dagger)$ for $k=1$ follows from the inequalities below
    -- $$ 2 a_{m+2}-1=a_{m+2}^{2}-\left(a_{m+2}-1\right)^{2} \leq a_{m}^{2}+2 a_{m+1}-\left(a_{m+2}-1\right)^{2} \leq 2 a_{m+1} $$
    simp
    have : 2 * a (m + 2) - (1 : ℝ) ≤ 2 * a (m + 1) := by
      trans a (m + 2 ) ^ 2 - (a (m + 2) - 1) ^ 2
      · apply le_of_eq; ring
      · apply le_trans <| sub_le_sub_right (ha_le _) _
        trans ↑(a m) ^ 2 + 2 * ↑(a (m + 1)) - (↑(a m) + 1 - 1) ^ 2 
        · gcongr
          · simp
          · norm_cast
        · apply sub_nonneg.mp <| le_of_eq (by ring)
    apply le_add_of_sub_left_le at this
    norm_cast at this
    trans (2 * a (m + 2)) / 2
    · simp
    trans (1 + 2 * a (m + 1)) / 2
    · gcongr
    · rw [Nat.add_div_of_dvd_left]
      all_goals simp
  | succ k ih =>
    -- From $$ a_{m+1}^{2} \leq a_{m+2 k+1}^{2} \leq a_{m+2 k-1}^{2}+2 a_{m+2 k} \leq a_{m+1}^{2}+2 a_{m+1} < \left(a_{m+1}+1\right)^{2} $$
    -- it follows that $a_{m+2 k+1}=a_{m+1}$ must hold. 
    have : a (m + 1 + 2 * (k + 1)) = a (m + 1) := by
      suffices : a (m + 1 + 2 * (k + 1)) ^ 2 < (a (m + 1) + 1) ^ 2
      · apply Nat.pow_lt_pow_iff_left (by simp) |>.mp at this
        apply le_antisymm
        · exact Nat.le_of_lt_succ this
        · rw [←ih.2]
          apply le_of_le_of_eq (ha_mono _) (by ring_nf)
      · apply Nat.cast_lt (α := ℝ) |>.mp
        simp
        rw [mul_add, mul_one, ←add_assoc]
        apply lt_of_le_of_lt (ha_le _)
        apply lt_of_le_of_lt (b := (a (m + 1)) ^ 2 + (2 : ℝ) * ↑(a (m + 1)))
        · gcongr
          · rw [←ih.2]
          · apply le_of_eq_of_le (by ring_nf) ih.1
        · apply sub_pos.mp
          ring_nf
          simp
    constructor
    · -- Furthermore, since $a_{m+2 k} \leq a_{m+1}$, we have
      -- $$ a_{m+2 k+2}^{2} \leq a_{m+2 k}^{2}+2 a_{m+2 k+1} \leq a_{m+1}^{2}+2 a_{m+1} < \left(a_{m+1}+1\right)^{2} $$ 
      -- from which it follows that $a_{m+2 k+2} \leq a_{m+1}$, which proves the assertion
      suffices : a (m + 2 + 2 * (k + 1)) ^ 2 < (a (m + 1) + 1) ^ 2
      · apply Nat.pow_lt_pow_iff_left (by simp) |>.mp at this
        exact Nat.le_of_lt_succ this
      · apply Nat.cast_lt (α := ℝ) |>.mp
        simp
        rw [mul_add, mul_one, ←add_assoc]
        apply lt_of_le_of_lt (ha_le _)
        apply lt_of_le_of_lt (b := (a (m + 1)) ^ 2 + (2 : ℝ) * ↑(a (m + 1)))
        · gcongr
          · exact ih.1
          · rw [←this]
            apply le_of_eq; ring_nf
        · apply sub_pos.mp
          ring_nf
          simp
    · exact this

/- If a sequence is monotone and bounded above, then it is eventually constant. -/
lemma eventualy_const {a : ℕ → ℕ} (ha : Monotone a) (hle : ∀ n, a n ≤ c) : ∃ N, ∀ n ≥ N, a n = a N := by
  let a₀ := ⨆ i, a i
  have : Filter.Tendsto a (Filter.atTop) (nhds a₀) := by
    refine tendsto_atTop_ciSup ha ?_
    refine bddAbove_def.mpr ?_
    use c
    simp [hle]
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp this 1 (by simp)
  have hN : ∀ n ≥ N, a n = a₀ := by
    intro n hn
    obtain h := hN n hn
    simp [dist, abs] at h
    rcases h with ⟨h₁, h₂⟩
    apply lt_add_of_sub_left_lt at h₁
    apply lt_add_of_sub_left_lt at h₂
    norm_cast at h₁ h₂
    apply le_antisymm
    · exact Nat.le_of_lt_succ h₁
    · exact Nat.le_of_lt_succ h₂
  use N
  intro n hn
  rw [hN n hn, hN N (by simp)]

/- Show that $r=2$ is the largest real number $r$ which satisfies the following condition:

If a sequence $a_{1}, a_{2}, \ldots$ of positive integers fulfills the inequalities

$$
a_{n} \leq a_{n+2} \leq \sqrt{a_{n}^{2}+r a_{n+1}}
$$

for every positive integer $n$, then there exists a positive integer $M$ such that $a_{n+2}=a_{n}$ for every $n \geq M$. -/
theorem inequalities_606096 :
    IsGreatest {r : ℝ | ∀ a : ℕ → ℕ, (∀ n, a n > 0 ∧ a n ≤ a (n + 2) ∧ a (n + 2) ≤ √(a n ^ 2 + r * a (n + 1))) → ∃ M, ∀ n ≥ M, a (n + 2) = a n} 2 := by
  constructor
  · intro a ha
    -- In order to finish the proof, it is enough to show that $a_{m+2 k}$ becomes constant after some value of $k$.
    have ha_le : ∀ n, a (n + 2) ^ 2 ≤ (a n : ℝ) ^ 2 + 2 * a (n + 1) := by
      intro n
      trans (√(a n ^ 2 + (2 : ℝ) * a (n + 1))) ^ 2
      · gcongr; apply (ha n).2.2
      · apply le_of_eq
        rw [sq_sqrt]
        positivity
    by_cases hm : ∃ m, a (m + 2) > a m
    · obtain ⟨m, hm⟩ := hm
      --  Since every $a_{m+2 k}$ is a positive integer less than or equal to $a_{m+1}$, there exists $k=K$ for which $a_{m+2 K}$ takes the maximum value. 
      obtain h := antitone_of_lt (fun n => (ha n).2.1) ha_le m hm
      let b (k : ℕ) := a (m + 2 + 2 * k) 
      have hmono : Monotone b := by
        apply monotone_nat_of_le_succ
        simp [b]
        simp [mul_add, mul_one, ←add_assoc]
        intro k
        apply le_of_eq_of_le (by ring_nf) (ha _).2.1
      have hle : ∀ k, b k ≤ a (m + 1) := by intros; apply (h _).1
      obtain ⟨M, hM⟩ := eventualy_const hmono hle
      -- By the monotonicity of $a_{m+2 k}$, it then follows that $a_{m+2 k}=a_{m+2 K}$ for all $k \geq K$.
      have h₁ : ∀ k, a (m + 2 + 2 * M + 2 * k) = a (m + 2 + 2 * M) := by
        intro k
        trans b (M + k)
        · simp [b]; ring_nf
        · rw [hM _ (by simp)]
      have h₂ : ∀ k, a (m + 2 + 2 * M + 2 * k + 1) = a (m + 1) := by
        intro k
        rw [←(h (M + k + 1)).2]
        ring_nf
      use m + 2 + 2 * M
      intro n hn
      let d := n - (m + 2 + 2 * M)
      let k := d / 2
      have hd : d = 2 * k + d % 2 := by exact Eq.symm (Nat.div_add_mod d 2)
      have hn_eq : n = m + 2 + 2 * M + 2 * k + d % 2 := by
        rw [add_assoc, ←hd]
        simp [d]
        rw [Nat.add_sub_cancel' hn]
      have hn_eq' : n + 2 = m + 2 + 2 * M + 2 * (k + 1) + d % 2 := by
        rw [hn_eq]; ring
      rw [hn_eq', hn_eq]
      mod_cases d % 2
      · have : d % 2 = 0 := by exact H
        simp [this]
        rw [h₁, h₁]
      · have : d % 2 = 1 := by exact H
        simp [this]
        rw [h₂, h₂]
    · simp at hm
      use 0
      intro n _
      apply le_antisymm (hm n) (ha n).2.1
  · -- First, let us assume that $r > 2$, and take a positive integer $a \geq 1 /(r-2)$. 
    intro r hr
    by_contra h_gt
    simp at h_gt
    let a₀ := ⌈1/ (r - 2)⌉₊
    have ha₀_pos : a₀ > 0 := by simp [a₀, h_gt]
    -- Then, if we let $a_{n}=a+\lfloor n / 2\rfloor$ for n ∈ ℕ
    let a (n : ℕ) := a₀ + n / 2
    -- the sequence $a_{n}$ satisfies the inequalities given in the problem.
    have ha_pos : ∀ n, a n > 0 := by intros; positivity
    have hmono : ∀ n, a n ≤ a (n + 2) := by simp [a]
    -- and $$ \sqrt{a_{n}^{2}+r a_{n+1}} \geq \sqrt{a_{n}^{2}+r a_{n}} \geq \sqrt{a_{n}^{2}+\left(2+\frac{1}{a}\right) a_{n}} \geq a_{n}+1=a_{n+2} $$
    have hle : ∀ n, a (n + 2) ≤ √(a n ^ 2 + r * a (n + 1)) := by
      intro n
      trans a n + 1
      · apply le_of_eq; simp [a]; ring
      · apply le_sqrt ?_ ?_ |>.mpr
        · trans a n ^ 2 + r * a n
          · rw [add_sq, add_assoc]
            gcongr
            apply add_le_of_le_sub_left
            trans (r - 2) * a n
            · trans (r - 2) * a₀ 
              · simp [a₀]
                trans (r - 2) * (r - 2)⁻¹
                · apply le_of_eq
                  rw [mul_inv_cancel₀ (ne_of_gt <| sub_pos.mpr h_gt)]
                · gcongr
                  · apply le_of_lt <| sub_pos.mpr h_gt
                  · exact Nat.le_ceil (r - 2)⁻¹
              · gcongr
                · apply le_of_lt <| sub_pos.mpr h_gt
                · simp [a]
            · apply le_of_eq; ring
          · simp [a]; gcongr; simp
        all_goals positivity
    -- but since $a_{n+2} > a_{n}$ for any $n$, we see that $r$ does not satisfy the condition given in the problem. 
    obtain ⟨M, hM⟩ := hr a (fun n => ⟨ha_pos n, hmono n, hle n⟩)
    specialize hM M
    simp [a] at hM


    