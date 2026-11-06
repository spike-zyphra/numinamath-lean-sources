import Mathlib

theorem algebra_107550 (f : ℤ → ℤ) :
    (∀ x y, f (x + y) = f x + f y + 2) ↔ ∃ a, ∀ x, f x = a * x - 2 := by
  constructor
  · -- First direction: assuming the functional equation, derive the existence of 'a'
    intro h
    have f0 : f 0 = -2 := by
      have h1 := h 0 0
      simp at h1 
      linarith
    use f 1 + 2
    intro x
    have eq1 : ∀ x : ℕ, f (x : ℤ) = (f 1 + 2) * (x : ℤ) - 2 := by
      intro x 
      induction x with
      | zero =>
        simp at * 
        <;> omega 
      | succ n ih =>
        have h11 : f ((↑(n + 1) : ℤ) : ℤ) = f (↑n + 1 : ℤ) := by 
          simp at * 
          all_goals omega 
        rw [h11] 
        have h22 := h (↑n : ℤ) 1 
        rw [h22] 
        rw [ih]
        all_goals simp 
        <;> ring 
    have eq2 : ∀ x : ℕ, f (-((x : ℤ))) = (f 1 + 2) * (-(x : ℤ)) - 2 := by
      intro x 
      induction x with 
      | zero =>
        simp at * 
        <;> omega 
      | succ n ih =>
        have h11 : f (-((↑(n + 1) : ℤ) : ℤ)) = f (-((↑n + 1 : ℤ) : ℤ)) := by 
          simp at * 
          all_goals omega 
        rw [h11] 
        have eq3 : f (-((↑n + 1 : ℤ) : ℤ)) = -4 - f (↑n + 1 : ℤ) := by
          have eq4 : f (0 : ℤ) = -2 := f0
          have eq5 := h (↑n + 1 : ℤ) (-((↑n + 1 : ℤ)))
          have eq6 : (↑n + 1 : ℤ) + (-((↑n + 1 : ℤ))) = (0 : ℤ) := by 
            omega 
          rw [eq6] at eq5 
          linarith 
        have eq41 : f (↑n + 1 : ℤ) = (f 1 + 2) * (↑n + 1 : ℤ) - 2 := by
          specialize eq1 (↑n + 1) 
          simpa using eq1 
        rw [eq3, eq41]
        all_goals simp 
        <;> ring 
    have eq3 (x : ℤ) : f x = (f 1 + 2) * x - 2 := by 
      by_cases h1 : x < 0 
      · -- x is negative
        have hx : x = -(x.natAbs : ℤ) := by 
          omega 
        rw [hx]
        have eq4 : f (-(x.natAbs : ℤ)) = (f 1 + 2) * (-(x.natAbs : ℤ)) - 2 := by
          apply eq2 x.natAbs
        linarith 
      · -- x ≥ 0 
        have h2 : x ≥ 0 := by 
          omega 
        if h3 : x = 0 then 
          rw [h3]
          all_goals linarith [f0]
        else 
          have h4 : x > 0 := by 
            omega 
          have hx : x = (x.natAbs : ℤ) := by 
            omega 
          rw [hx]
          have hx2 : (x.natAbs : ℤ) ≥ 0 := by 
            omega 
          have eq4 : f (x.natAbs : ℤ) = (f 1 + 2) * (x.natAbs : ℤ) - 2 := by
            apply eq1 x.natAbs
          linarith 
    specialize eq3 x 
    simpa using eq3
  · -- Second direction: assuming a exists, prove the functional equation
    rintro ⟨a, ha⟩
    intro x y
    have h1 : f (x + y) = a * (x + y) - 2 := ha (x + y)
    have h2 : f x = a * x - 2 := ha x
    have h3 : f y = a * y - 2 := ha y
    rw [h1, h2, h3]
    all_goals ring