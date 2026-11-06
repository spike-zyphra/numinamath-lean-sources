import Mathlib

/-Solve the equation in natural numbers
abc+ab+bc+ac+a+b+c=164
In your answer, specify the product abc.-/

theorem algebra_197969 {a b c: ℕ} (h: a * b * c + a * b + b * c + a * c + a + b + c = 164) :
    a * b * c = 80 ∨ a * b * c = 0:= by

  replace h: a * b * c + a * b + b * c + a * c + a + b + c + 1 = 165 := by
    rw [h]
  -- we factor the left-hand side
  have eq: a * b * c + a * b + b * c + a * c + a + b + c + 1 = (a + 1) * (b + 1) * (c + 1) := by
    ring
  rw [eq] at h
  clear eq
  by_cases l: a = 0 ∨ b = 0 ∨ c = 0

  -- if one of the variables is zero, we can conclude abc=0
  .
    have o: a * b * c = 0 := by
      rcases l with l | l | l
      all_goals simp [l]
    simp [o]

  -- if none of the variables is zero, we can conclude abc=80
  .
    left
    set p:= a + 1
    set q:= b + 1
    set r:= c + 1
    rw [show a = p - 1 by omega]
    rw [show b = q - 1 by omega]
    rw [show c = r - 1 by omega]

    -- then we give bound of p q r
    have lp: 2 ≤ p := by omega
    have lq: 2 ≤ q := by omega
    have lr: 2 ≤ r := by omega
    have rp: p ≤ 42 := by
      by_contra! l
      have o: 84 < p * q := by nlinarith
      nlinarith
    have rq: q ≤ 42 := by
      by_contra! l
      have o: 84 < p * q := by nlinarith
      nlinarith
    have rr: r ≤ 42 := by
      by_contra! l
      have o: 84 < q * r := by nlinarith
      nlinarith
    clear_value p q r
    clear l
    have d: p ∈ Nat.divisors 165 := by
      simp
      rw [← h]
      rw [show p * q * r = q * r * p by ring]
      simp
    rw [show Nat.divisors 165 = {1, 3, 5, 11, 15, 33, 55, 165} by native_decide] at d
    simp at d
    rcases d with d | d | d | d | d | d | d | d
    all_goals try omega

    -- p = 3
    .
      simp [d] at *
      replace h: q * r = 55 := by
        rw [show 3 * q * r = 3 * (q * r) by ring] at h
        omega
      have t: q ∈ Nat.divisors 55 := by
        simp
        rw [← h]
        simp
      rw [show Nat.divisors 55 = {1, 5, 11, 55} by native_decide] at t
      simp at t
      rcases t with t | t | t | t
      all_goals try omega
      .
        simp [t] at h
        replace h: r = 11 := by omega
        simp [t, h]
      .
        simp [t] at h
        replace h: r = 5 := by omega
        simp [t, h]

    -- p = 5
    .
      simp [d] at *
      replace h: q * r = 33 := by
        rw [show 5 * q * r = 5 * (q * r) by ring] at h
        omega
      have t: q ∈ Nat.divisors 33 := by
        simp
        rw [← h]
        simp
      rw [show Nat.divisors 33 = {1, 3, 11, 33} by native_decide] at t
      simp at t
      rcases t with t | t | t | t
      all_goals try omega
      .
        simp [t] at h
        replace h: r = 11 := by omega
        simp [t, h]
      .
        simp [t] at h
        replace h: r = 3 := by omega
        simp [t, h]
      .
        simp [t] at h
        simp [h] at lr

    -- p = 11
    .
      simp [d] at *
      replace h: q * r = 15 := by
        rw [show 11 * q * r = 11 * (q * r) by ring] at h
        omega
      have t: q ∈ Nat.divisors 15 := by
        simp
        rw [← h]
        simp
      rw [show Nat.divisors 15 = {1, 3, 5, 15} by native_decide] at t
      simp at t
      rcases t with t | t | t | t
      all_goals try omega
      .
        simp [t] at h
        replace h: r = 5 := by omega
        simp [t, h]
      .
        simp [t] at h
        replace h: r = 3 := by omega
        simp [t, h]
      .
        simp [t] at h
        simp [h] at lr

    -- p = 15
    .
      simp [d] at *
      replace h: q * r = 11 := by
        rw [show 15 * q * r = 15 * (q * r) by ring] at h
        omega
      have t: q ∈ Nat.divisors 11 := by
        simp
        rw [← h]
        simp
      rw [show Nat.divisors 11 = {1, 11} by native_decide] at t
      simp at t
      rcases t with t | t
      .
        simp [t] at lq
      .
        simp [t] at h
        simp [h] at lr

    -- p = 33
    .
      simp [d] at *
      replace h: q * r = 5 := by
        rw [show 33 * q * r = 33 * (q * r) by ring] at h
        omega
      have t: q ∈ Nat.divisors 5 := by
        simp
        rw [← h]
        simp
      rw [show Nat.divisors 5 = {1, 5} by native_decide] at t
      simp at t
      rcases t with t | t
      .
        simp [t] at lq
      .
        simp [t] at h
        simp [h] at lr