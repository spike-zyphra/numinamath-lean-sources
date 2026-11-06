import Mathlib

/- Six positive integers are written on the faces of a cube. Each vertex is labeled with the product of the three numbers on the faces adjacent to the vertex. If the sum of the numbers on the vertices is equal to $1001$, then what is the sum of the numbers written on the faces? -/
theorem algebra_11617 (a b c d e f : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (h : a * b * c + a * e * c + a * b * f + a * e * f + d * b * c + d * e * c + d * b * f + d * e * f = 1001) :
  a + b + c + d + e + f = 31 := by
  -- We have (a + d) * (b + e) * (c + f) = 1001.
  have heq : (a + d) * (b + e) * (c + f) = a * b * c + a * e * c + a * b * f + a * e * f + d * b * c + d * e * c + d * b * f + d * e * f := by
    ring
  rw [<-heq] at h
  clear heq
  -- Lemma: If 2 ≤ a ≤ b ≤ c and a * b * c = 1001, then (a, b, c) = (7, 11, 13).
  have lm (a b c : ℕ) (ha : 2 ≤ a) (hb : a ≤ b) (hc : b ≤ c) (heq : a * b * c = 1001) : (a, b, c) = (7, 11, 13) := by
    let x : ℕ × ℕ := (a * b, c)
    have h₀ : x.1 * x.2 = 1001 ∧ 1001 ≠ 0 := by
      rw [heq]
      simp
    rw [<-Nat.mem_divisorsAntidiagonal] at h₀
    -- Use the computer to find the factors of 1001 (native_decide is necessary).
    rw [show Nat.divisorsAntidiagonal 1001 = {(1, 1001), (7, 143), (11, 91), (13, 77), (77, 13), (91, 11), (143, 7), (1001, 1)} by native_decide] at h₀
    simp at h₀
    obtain h | h | h | h | h | h | h | h := h₀
    . -- Case of (a * b, c) = (1, 1001): rejected.
      replace h₁ : x.1 ≠ 1 := by
        simp [x, -mul_eq_one]
        nlinarith only [ha, hb]
      absurd h₁
      rw [h]
    . -- Case of (a * b, c) = (7, 143): rejected.
      let y : ℕ × ℕ := (a, b)
      have h₁ : y.1 * y.2 = 7 ∧ 7 ≠ 0 := by
        simp [y]
        calc
          a * b = x.1 := by simp
          _ = 7 := by rw [h]
      rw [<-Nat.mem_divisorsAntidiagonal] at h₁
      -- Use the computer to find the factors of 7 (native_decide is necessary).
      rw [show Nat.divisorsAntidiagonal 7 = {(1, 7), (7, 1)} by native_decide] at h₁
      simp at h₁
      obtain h₁ | h₁ := h₁
      . have h : a = 1 := by
          calc
            a = y.1 := by simp
            _ = 1 := by rw [h₁]
        omega
      . have h : b = 1 := by
          calc
            b = y.2 := by simp
            _ = 1 := by rw [h₁]
        omega
    . -- Case of (a * b, c) = (11, 91): rejected.
      let y : ℕ × ℕ := (a, b)
      have h₁ : y.1 * y.2 = 11 ∧ 11 ≠ 0 := by
        simp [y]
        calc
          a * b = x.1 := by simp
          _ = 11 := by rw [h]
      rw [<-Nat.mem_divisorsAntidiagonal] at h₁
      -- Use the computer to find the factors of 11 (native_decide is necessary).
      rw [show Nat.divisorsAntidiagonal 11 = {(1, 11), (11, 1)} by native_decide] at h₁
      simp at h₁
      obtain h₁ | h₁ := h₁
      . have h : a = 1 := by
          calc
            a = y.1 := by simp
            _ = 1 := by rw [h₁]
        omega
      . have h : b = 1 := by
          calc
            b = y.2 := by simp
            _ = 1 := by rw [h₁]
        omega
    . -- Case of (a * b, c) = (13, 77): rejected.
      let y : ℕ × ℕ := (a, b)
      have h₁ : y.1 * y.2 = 13 ∧ 13 ≠ 0 := by
        simp [y]
        calc
          a * b = x.1 := by simp
          _ = 13 := by rw [h]
      rw [<-Nat.mem_divisorsAntidiagonal] at h₁
      -- Use the computer to find the factors of 13 (native_decide is necessary).
      rw [show Nat.divisorsAntidiagonal 13 = {(1, 13), (13, 1)} by native_decide] at h₁
      simp at h₁
      obtain h₁ | h₁ := h₁
      . have h : a = 1 := by
          calc
            a = y.1 := by simp
            _ = 1 := by rw [h₁]
        omega
      . have h : b = 1 := by
          calc
            b = y.2 := by simp
            _ = 1 := by rw [h₁]
        omega
    . -- Case of (a * b, c) = (77, 13): the only possibility.
      let y : ℕ × ℕ := (a, b)
      have h₁ : y.1 * y.2 = 77 ∧ 77 ≠ 0 := by
        simp [y]
        calc
          a * b = x.1 := by simp
          _ = 77 := by rw [h]
      rw [<-Nat.mem_divisorsAntidiagonal] at h₁
      -- Use the computer to find the factors of 77 (native_decide is necessary).
      rw [show Nat.divisorsAntidiagonal 77 = {(1, 77), (7, 11), (11, 7), (77, 1)} by native_decide] at h₁
      simp at h₁
      obtain h₁ | h₁ | h₁ | h₁ := h₁
      . have h : a = 1 := by
          calc
            a = y.1 := by simp
            _ = 1 := by rw [h₁]
        omega
      . replace ha : a = 7 := by
          calc
            a = y.1 := by simp
            _ = 7 := by rw [h₁]
        replace hb : b = 11 := by
          calc
            b = y.2 := by simp
            _ = 11 := by rw [h₁]
        replace hc : c = 13 := by
          calc
            c = x.2 := by simp
            _ = 13 := by rw [h]
        simp
        tauto
      -- All remaining goals is impossible because a > b.
      all_goals
        have h₂ : a > b := by
          calc
            a = y.1 := by simp
            _ > y.2 := by rw [h₁]; norm_num
            _ = b := by simp
        absurd h₂
        simp
        exact hb
    . -- Case of (a * b, c) = (91, 11): rejected.
      let y : ℕ × ℕ := (a, b)
      have h₁ : y.1 * y.2 = 91 ∧ 91 ≠ 0 := by
        simp [y]
        calc
          a * b = x.1 := by simp
          _ = 91 := by rw [h]
      rw [<-Nat.mem_divisorsAntidiagonal] at h₁
      -- Use the computer to find the factors of 91 (native_decide is necessary).
      rw [show Nat.divisorsAntidiagonal 91 = {(1, 91), (7, 13), (13, 7), (91, 1)} by native_decide] at h₁
      simp at h₁
      obtain h₁ | h₁ | h₁ | h₁ := h₁
      . have h : a = 1 := by
          calc
            a = y.1 := by simp
            _ = 1 := by rw [h₁]
        omega
      . have h : b > c := by
          calc
            b = y.2 := by simp
            _ = 13 := by rw [h₁]
            _ > 11 := by norm_num
            _ = x.2 := by rw [h]
            _ = c := by simp
        absurd h
        simp
        exact hc
      -- All remaining goals is impossible because a > b.
      all_goals
        have h₂ : a > b := by
          calc
            a = y.1 := by simp
            _ > y.2 := by rw [h₁]; norm_num
            _ = b := by simp
        absurd h₂
        simp
        exact hb
    . -- Case of (a * b, c) = (143, 7): rejected.
      let y : ℕ × ℕ := (a, b)
      have h₁ : y.1 * y.2 = 143 ∧ 143 ≠ 0 := by
        simp [y]
        calc
          a * b = x.1 := by simp
          _ = 143 := by rw [h]
      rw [<-Nat.mem_divisorsAntidiagonal] at h₁
      -- Use the computer to find the factors of 91 (native_decide is necessary).
      rw [show Nat.divisorsAntidiagonal 143 = {(1, 143), (11, 13), (13, 11), (143, 1)} by native_decide] at h₁
      simp at h₁
      obtain h₁ | h₁ | h₁ | h₁ := h₁
      . have h : a = 1 := by
          calc
            a = y.1 := by simp
            _ = 1 := by rw [h₁]
        omega
      . have h : b > c := by
          calc
            b = y.2 := by simp
            _ = 13 := by rw [h₁]
            _ > 7 := by norm_num
            _ = x.2 := by rw [h]
            _ = c := by simp
        absurd h
        simp
        exact hc
      -- All remaining goals is impossible because a > b.
      all_goals
        have h₂ : a > b := by
          calc
            a = y.1 := by simp
            _ > y.2 := by rw [h₁]; norm_num
            _ = b := by simp
        absurd h₂
        simp
        exact hb
    . -- Case of (a * b, c) = (1001, 1): rejected.
      have h : c = 1 := by
        calc
          c = x.2 := by simp
          _ = 1 := by rw [h]
      omega
  replace lm (a b c : ℕ) (ha : 2 ≤ a) (hb : a ≤ b) (hc : b ≤ c) (heq : a * b * c = 1001) : a + b + c = 31 := by
    have g : (a, b, c) = (7, 11, 13) := by
      apply lm
      assumption'
    calc
      a + b + c = (a, b, c).1 + (a, b, c).2.1 + (a, b, c).2.2 := by simp
      _ = 7 + 11 + 13 := by rw [g]
      _ = 31 := by norm_num
  replace lm (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (heq : a * b * c = 1001) : a + b + c = 31 := by
    -- Tree of decision:
      -- a ≤ b
        -- b ≤ c → a ≤ b ≤ c
        -- c < b
          -- c ≤ a → c ≤ a ≤ b
          -- a < c → a < c < b
        -- b < a
          -- b ≤ c
            -- c ≤ a → b ≤ c ≤ a
            -- a < c → b < a < c
          -- c < b → c < b < a
    by_cases g₀ : a ≤ b
    . -- Case of a ≤ b.
      by_cases g₁ : b ≤ c
      . -- Cases of b ≤ c.
        apply lm a b c
        assumption'
      . -- Cases of c < b.
        by_cases g₂ : c ≤ a
        . -- Cases of c ≤ a.
          rw [show a + b + c = c + a + b by ac_rfl]
          apply lm c a b
          assumption'
          rw [show c * a * b = a * b * c by ac_rfl]
          exact heq
        . -- Cases of a < c.
          rw [show a + b + c = a + c + b by ac_rfl]
          apply lm a c b
          assumption'
          repeat omega
          rw [show a * c * b = a * b * c by ac_rfl]
          exact heq
    . -- Cases of b < a.
      by_cases g₁ : b ≤ c
      . -- Cases of b ≤ c.
        by_cases g₂ : c ≤ a
        . -- Cases of c ≤ a.
          rw [show a + b + c = b + c + a by ac_rfl]
          apply lm b c a
          assumption'
          rw [show b * c * a = a * b * c by ac_rfl]
          exact heq
        . -- Cases of a < c.
          rw [show a + b + c = b + a + c by ac_rfl]
          apply lm b a c
          assumption'
          repeat omega
          rw [show b * a * c = a * b * c by ac_rfl]
          exact heq
      . -- Cases of c < b.
        rw [show a + b + c = c + b + a by ac_rfl]
        apply lm c b a
        assumption'
        repeat omega
        rw [show c * b * a = a * b * c by ac_rfl]
        exact heq
  suffices g : (a + d) + (b + e) + (c + f) = 31 by
    rw [<-g]
    ac_rfl
  apply lm (a + d) (b + e) (c + f)
  omega
  omega
  omega
  exact h
