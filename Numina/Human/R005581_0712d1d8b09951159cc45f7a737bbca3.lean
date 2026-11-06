import Mathlib

open Real

/-Find all ordered triples $(a, b, c)$ of positive reals that satisfy: $\lfloor a\rfloor b c=3, a\lfloor b\rfloor c=4$, and $a b\lfloor c\rfloor=5$, where $\lfloor x\rfloor$ denotes the greatest integer less than or equal to $x$.-/
theorem algebra_608963 (a b c : ℝ) (apos : 0 < a) (bpos : 0 < b) (cpos : 0 < c) :
⌊a⌋ * b * c = 3 ∧ a * ⌊b⌋ * c = 4 ∧ a * b * ⌊c⌋ = 5 ↔ (a, b, c) =
(√30 / 3, √30 / 4, 2 * √30 / 5) ∨ (a, b, c) = (√30 / 3, √30 / 2, √30 / 5) := by
  constructor
  -- Denote $p$ to be the product of $a$, $b$ and $c$ and $q$ to be the product of $⌊a⌋$, $⌊b⌋$ and $⌊c⌋$
  · rintro ⟨h1, h2, h3⟩; let p := a * b * c; let q := ⌊a⌋ * ⌊b⌋ * ⌊c⌋
    have : 0 ≤ ⌊a⌋ := by simp [Int.le_floor]; positivity
    have : 0 ≤ ⌊c⌋ := by simp [Int.le_floor]; positivity
  -- Prove that $q$ is positive
    have qpos : 0 < q := by
      dsimp [q]; apply mul_pos; apply mul_pos
      · by_contra!; simp [Int.floor_le_iff] at this
        replace this : ⌊a⌋ = 0 := by
          simp [Int.floor_eq_iff]; constructor
          · exact le_of_lt apos
          exact this
        simp [this] at h1
      · by_contra!; simp [Int.floor_le_iff] at this
        replace this : ⌊b⌋ = 0 := by
          simp [Int.floor_eq_iff]; constructor
          · exact le_of_lt bpos
          exact this
        simp [this] at h2
      · by_contra!; simp [Int.floor_le_iff] at this
        replace this : ⌊c⌋ = 0 := by
          simp [Int.floor_eq_iff]; constructor
          · exact le_of_lt cpos
          exact this
        simp [this] at h3
  -- Prove that $p=√(60/q)$
    have hpq : p = √((60 : ℝ) / q) := by
      symm; rw [sqrt_eq_iff_eq_sq, div_eq_iff, show (60:ℝ) = 3*4*5 by norm_num]
      rw [← h1, ← h2, ← h3]; dsimp [p, q]; push_cast; ring
      all_goals positivity
  -- Prove that $p$ is between $5$ and $6$
    have pbd : 5 ≤ p ∧ p ≤ 6 := by
      dsimp [p]; constructor
      · rw [← h3, mul_le_mul_left]; exact Int.floor_le c; positivity
      rw [show (6:ℝ) = 2*3 by norm_num, ← h1, mul_assoc]
      rw [show 2*(⌊a⌋*b*c) = 2*⌊a⌋*(b*c) by ring, mul_le_mul_right, two_mul, ← sub_le_iff_le_add]
      nth_rw 1 [← Int.fract_add_floor a, add_sub_cancel_right]; calc
        _ ≤ (1:ℝ) := by norm_cast; exact le_of_lt (Int.fract_lt_one a)
        _ ≤ _ := by
          norm_cast; by_contra!; simp [Int.floor_lt] at this
          replace this : ⌊a⌋ = 0 := by
            simp [Int.floor_eq_iff]; constructor
            · exact le_of_lt apos
            exact this
          simp [this] at h1
      positivity
  -- Prove that $q$ is $2$
    have qeq2 : q = 2 := by
      rw [hpq] at pbd; rcases pbd with ⟨qbd1, qbd2⟩
      rw [sqrt_le_iff, div_le_iff₀'] at qbd2; norm_num at qbd2
      rw [le_sqrt, le_div_iff₀] at qbd1; norm_num at qbd1
      norm_cast at qbd1 qbd2; omega; all_goals positivity
  -- Plug in $q=2$ at hpq and simplify it to $p=√30$
    rw [qeq2] at hpq; norm_num at hpq
    dsimp [p] at hpq; dsimp [q] at qeq2
  -- Discuss all possible values for $⌊a⌋$, $⌊b⌋$ and $⌊c⌋$
    have : ⌊c⌋ ∣ 2 ^ 1 := by use ⌊a⌋*⌊b⌋; rw [← qeq2]; ring
    rw [dvd_prime_pow Int.prime_two] at this; rcases this with ⟨i, ⟨hi1, hi2⟩⟩
    rw [Int.associated_iff] at hi2; rcases hi2 with hc|hc
    · interval_cases i; simp at hc; simp [hc] at qeq2
      have : ⌊a⌋ ∣ 2 ^ 1 := by use ⌊b⌋; rw [← qeq2]; ring
      rw [dvd_prime_pow Int.prime_two] at this; rcases this with ⟨j, ⟨hj1, hj2⟩⟩
      rw [Int.associated_iff] at hj2; rcases hj2 with ha|ha
      · interval_cases j
        · simp at ha; simp [ha] at qeq2
          simp [ha] at h1; simp [hc] at h3
          simp [qeq2] at h2; rw [mul_comm, ← mul_assoc, show (4:ℝ) = 2*2 by norm_num] at h2
          apply mul_right_cancel₀ at h2; right; simp
          repeat rw [eq_div_iff]
          rw [← h1, ← h2, ← h3, ← hpq]; ring_nf; simp; any_goals norm_num
        simp at ha; rw [ha, mul_assoc, mul_comm, ← eq_div_iff] at h1
        simp [Int.floor_eq_iff] at ha; norm_num at ha h1
        rw [mul_assoc, h1, ← eq_div_iff] at hpq; suffices : 3 < a; linarith
        rw [hpq, lt_div_iff₀, lt_sqrt]; all_goals norm_num
      have : ⌊a⌋ < 0 := by simp [ha]
      omega
      left; simp; simp at hc; simp [hc, mul_left_eq_self₀] at qeq2
      rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at qeq2
      rcases qeq2 with ⟨ha, hb⟩|⟨ha, hb⟩
      · simp [ha] at h1; simp [hb] at h2
        simp [hc] at h3
        rw [← hpq, eq_div_iff, eq_div_iff, eq_div_iff, ← mul_assoc, ← h1, ← h2]
        nth_rw 11 [mul_comm]; rw [h3]; ring_nf; simp; all_goals norm_num
      omega
    have : ⌊c⌋ < 0 := by simp [hc]
    omega
-- Conversely, it is straightforward to check that the given values are solution to the equations in question
  simp; intro h; rcases h with ⟨ha, hb, hc⟩|⟨ha, hb, hc⟩
  · have fla : ⌊a⌋ = 1 := by
      rw [Int.floor_eq_iff, ha]; norm_num
      rw [le_div_iff₀, le_sqrt, div_lt_iff₀, sqrt_lt]
      all_goals norm_num
    have flb : ⌊b⌋ = 1 := by
      rw [Int.floor_eq_iff, hb]; norm_num
      rw [le_div_iff₀, le_sqrt, div_lt_iff₀, sqrt_lt]
      all_goals norm_num
    have flc : ⌊c⌋ = 2 := by
      rw [Int.floor_eq_iff, hc]; norm_num
      rw [le_div_iff₀, mul_le_mul_left, le_sqrt, div_lt_iff₀, ← lt_div_iff₀', sqrt_lt]
      all_goals norm_num
    simp [fla, flb, flc]; rw [ha, hb, hc]; ring_nf; rw [sq_sqrt]; all_goals norm_num
  have fla : ⌊a⌋ = 1 := by
    rw [Int.floor_eq_iff, ha]; norm_num
    rw [le_div_iff₀, le_sqrt, div_lt_iff₀, sqrt_lt]
    all_goals norm_num
  have flb : ⌊b⌋ = 2 := by
    rw [Int.floor_eq_iff, hb]; norm_num
    rw [le_div_iff₀, le_sqrt, div_lt_iff₀, sqrt_lt]
    all_goals norm_num
  have flc : ⌊c⌋ = 1 := by
    rw [Int.floor_eq_iff, hc]; norm_num
    rw [le_div_iff₀, le_sqrt, div_lt_iff₀, sqrt_lt]
    all_goals norm_num
  simp [fla, flb, flc]; rw [ha, hb, hc]; ring_nf; rw [sq_sqrt]; all_goals norm_num