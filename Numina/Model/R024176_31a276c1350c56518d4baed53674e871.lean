import Mathlib


lemma lemma_1
    {a : ℕ → ℤ}
    (ha1 : ∀ n : ℕ, Odd n → a n = a (n - 1) + n)
    (ha2 : ∀ n : ℕ, Even n → a n = a (n - 1) - n) :
    ∀ k ≥ 2, Even k → a k = a 2 - (k - 2)/2 := by
  intro k hk hke
  have h1 : k ≥ 2 := hk
  have hk2 : Even k := hke
  rcases hk2 with ⟨m, hm⟩
  have h2 : m ≥ 1 := by
    by_contra h
    push_neg at h
    have : m = 0 := by omega
    rw [this] at hm
    omega
  have eq1 : ∀ (m : ℕ), m ≥ 1 → a (2 * m) = a 2 - ((2 * m) - 2) / 2 := by
    intro m hm
    have base1 : a (2 * 1) = a 2 - ((2 * 1) - 2) / 2 := by
      simp
    have step1 : ∀ (n : ℕ), n ≥ 1 → a (2 * n) = a 2 - ((2 * n) - 2) / 2 → a (2 * (n + 1)) = a 2 - ((2 * (n + 1)) - 2) / 2 := by
      intro n hn h
      have eq3 : a (2 * (n + 1)) = a (2 * n + 2) := by ring_nf
      rw [eq3]
      have eq4 : a (2 * n + 2) = a (2 * n + 1) - (2 * n + 2 : ℤ) := by
        have hne : Even (2 * n + 2) := by
          simp [Nat.even_mul, Nat.even_add]
        specialize ha2 (2 * n + 2) hne
        simpa using ha2
      have eq5 : a (2 * n + 1) = a (2 * n) + (2 * n + 1 : ℤ) := by
        have hno : Odd (2 * n + 1) := by
          simp [Nat.odd_mul, Nat.odd_add]
        specialize ha1 (2 * n + 1) hno
        simpa using ha1
      rw [eq4, eq5]
      omega
    exact Nat.le_induction base1 step1 m hm
  rw [show k = 2 * m by linarith [hm]]
  apply eq1 m (by omega)


theorem algebra_4898
  (a : ℕ → ℤ)
  (ha : ∀ n, Odd n → a n = a (n - 1) + n)
  (ha' : ∀ n, Even n → a n = a (n - 1) - n)
  (ha'' : a 2016 = 1) :
  a 2 = 1008 := by

  have eq3 : a 2016 = a 2 - (2016 - 2)/2 := by
    apply lemma_1 ha ha' 2016 (by norm_num) (by decide)
  have eq3' : a 2 - (2016 - 2)/2 = 1 := by
    linarith [ha'', eq3]
  norm_num at eq3'
  all_goals omega