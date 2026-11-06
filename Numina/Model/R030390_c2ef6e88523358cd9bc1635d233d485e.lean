import Mathlib


theorem number_theory_283175 :
  {(a, b) : ℕ × ℕ | Nat.gcd a b = 21 ∧ Nat.lcm a b = 3969} =
  {(21, 3969), (3969, 21), (147, 567), (567, 147)} := by
  ext ⟨a, b⟩
  simp
  constructor
  · -- First, we show that if (a, b) satisfies gcd 21 and lcm 3969, then it's in the set.
    rintro ⟨h1, h2⟩
    have h3 : a.gcd b * (a.lcm b) = a * b := by
      rw [Nat.gcd_mul_lcm]
    rw [h1, h2] at h3
    have h4 : a * b = 83349 := by
      nlinarith
    have h5 : 21 ∣ a := by
      have h6 : Nat.gcd a b = 21 := h1
      have h7 : Nat.gcd a b ∣ a := by exact Nat.gcd_dvd_left a b
      rw [h6] at h7
      exact h7
    have h8 : 21 ∣ b := by
      have h9 : Nat.gcd a b = 21 := h1
      have h10 : Nat.gcd a b ∣ b := by exact Nat.gcd_dvd_right a b
      rw [h9] at h10
      exact h10
    rcases h5 with ⟨m, hm⟩
    rcases h8 with ⟨n, hn⟩
    have h10 : Nat.gcd m n = 1 := by
      have h7 : Nat.gcd (21 * m) (21 * n) = 21 * (Nat.gcd m n) := by
        rw [Nat.gcd_mul_left]
      have h12 : Nat.gcd (21 * m) (21 * n) = 21 := by
        rw [show 21 * m = a by nlinarith, show 21 * n = b by nlinarith]
        exact h1
      rw [h7] at h12
      omega
    have h11 : Nat.lcm m n = 189 := by
      have h12 : Nat.lcm (21 * m) (21 * n) = 21 * (Nat.lcm m n) := by
        rw [Nat.lcm_mul_left]
      have h13 : Nat.lcm (21 * m) (21 * n) = 3969 := by
        rw [show 21 * m = a by nlinarith, show 21 * n = b by nlinarith]
        exact h2
      rw [h12] at h13
      omega
    have h13 : m * n = 189 := by
      calc
        m * n = Nat.gcd m n * (Nat.lcm m n) := by rw [Nat.gcd_mul_lcm]
        _ = 1 * (Nat.lcm m n) := by rw [h10]
        _ = 1 * 189 := by rw [h11]
        _ = 189 := by norm_num
    have h14 : m ∣ 189 := by
      use n
      all_goals
        nlinarith
    have h16 : m ≤ 189 := by
      exact Nat.le_of_dvd (by norm_num) h14
    have h17 : m ∣ 189 := h14
    have h18 : m ≤ 189 := h16
    interval_cases m <;> try { 
      omega 
    } <;> try { 
      have : n ≤ 189 := by 
        nlinarith 
      interval_cases n <;> norm_num [hm, hn] at *
      <;> tauto 
    }
  · -- Show that these four pairs satisfy gcd 21 and lcm 3969.
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · constructor
      · norm_num [Nat.gcd]
      · norm_num [Nat.lcm]
    · constructor
      · norm_num [Nat.gcd]
      · norm_num [Nat.lcm]
    · constructor
      · norm_num [Nat.gcd]
      · norm_num [Nat.lcm]
    · constructor
      · norm_num [Nat.gcd]
      · norm_num [Nat.lcm]