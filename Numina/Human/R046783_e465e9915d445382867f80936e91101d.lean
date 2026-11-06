import Mathlib

theorem algebra_317602 :
  IsGreatest {x : ℤ | ∃ a b c : ℤ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b + b * c = 518 ∧ a * b - a * c = 360 ∧ x = a * b * c} 1008 := by 
  unfold IsGreatest -- Simplify the goal to show existence and upper bound.
  constructor -- Split into two parts: showing that 1008 is in the set and it's an upper bound.
  · simp
    use 72
    constructor
    norm_num
    use 7
    constructor
    norm_num
    use 2
    constructor
    norm_num
    constructor
    norm_num
    constructor
    norm_num
    norm_num
  · unfold upperBounds
    simp
    intro x a ha b hb c hc h1 h2 h3 
    have eq1 : c * (a + b) = 2 * 79 := by 
      nlinarith
    have prime1 : Nat.Prime 2 := by norm_num
    have prime2 : Nat.Prime 79 := by norm_num
    have eq_c_or_mul : 79 ∣ c ∨ 79 ∣ (a + b):= by 
      refine Prime.dvd_or_dvd ?_ ?_
      simpa
      rw [eq1]
      norm_num
    obtain hc1 | hc2 := eq_c_or_mul
    -- the case 79 divides c
    · obtain ⟨k, hkeq⟩ := hc1
      rw [hkeq] at eq1
      have eq_aux1 : k * (a + b) = 2 := by nlinarith
      have kpos : k > 0 := by nlinarith
      have kgeone : k ≥ 1 := kpos
      have able : (a + b) ≤ 2 := by 
        nlinarith
      have abge : a + b ≥ 2 := by 
        nlinarith
      have abeq : a + b = 2 := by
        exact eq_of_le_of_le able abge
      have keq : k = 1 := by nlinarith
      rw [keq] at hkeq
      simp at hkeq
      have aeq : a = 1 := by 
        nlinarith
      have beq : b = 1 := by
        nlinarith
      rw [aeq, beq, hkeq] at h3
      rw [h3]
      simp
    · -- the case 79 divides a+b
      obtain ⟨k, hkeq⟩ := hc2
      rw [hkeq] at eq1
      have kpos : k > 0 := by nlinarith
      have kgeone : k ≥ 1 := kpos
      have ckeq : c * k = 2 := by 
        nlinarith
      have cge : c ≥ 1 := hc
      have cle : c ≤ 2 := by nlinarith
      interval_cases c
      -- case c = 1
      simp_all
      -- use inequality to prove the goal 
      have ineq_aux : 2 * a * b ≤  (a * b + b) + (a * b - a) + (a + b) := by 
        linarith

      rw [h1,h2,hkeq] at ineq_aux
      nlinarith
      -- cases c = 2
      simp_all
      have aeq : a = 79 - b := by nlinarith
      rw [aeq]
      nlinarith

  