import Mathlib

/-
5. Bas has coloured each of the positive integers. He had several colours at his disposal. His colouring satisfies the following requirements:

- each odd integer is coloured blue;
- each integer $n$ has the same colour as $4 n$;
- each integer $n$ has the same colour as at least one of the integers $n+2$ and $n+4$.

Prove that Bas has coloured all integers blue.

 -/
 
theorem number_theory_173433 {blue: Set ℕ} (h1: ∀ n, Odd n → n ∈ blue) (h2: ∀ n, 0 < n → (n ∈ blue ↔ 4 * n ∈ blue))
 (h3: ∀ n, 0 < n → (n ∈ blue →  n + 2 ∈ blue ∨ n + 4 ∈ blue))
 (h3': ∀ n, 0 < n → (¬ n ∈ blue → ¬ n + 2 ∈ blue ∨ ¬ n + 4 ∈ blue)): ∀ n, 0 < n → n ∈ blue := by
    by_contra! h
    obtain ⟨k, h⟩ := h
    rcases h with ⟨hk, h⟩

     -- k is even
    have ok: Even k := by
      by_contra! ok
      simp at ok
      specialize h1 k ok
      tauto
    rw [even_iff_exists_two_mul] at ok
    obtain ⟨m, hm⟩ := ok
    have lm: 0 < m := by omega

    -- 8m is not blue
    have om: ¬ 8 * m ∈ blue := by
      by_contra! om
      specialize h2 (2 * m)
      simp [lm] at h2
      rw [show 4 * (2 * m) = 8 * m by ring] at h2
      rw [← h2] at om
      rw [← hm] at om
      tauto

    -- then we show that 8m + 2 is not blue
    have i: ¬ 8 * m + 2 ∈ blue := by
      by_contra! i
      specialize h3' (8 * m)
      have o: 0 < 8 * m := by omega
      simp [o, om] at h3'
      simp [i] at h3'
      specialize h2 (2 * m + 1)
      have u: 0 < 2 * m + 1 := by
        omega
      simp [u] at h2
      rw [show 4 * (2 * m + 1) = 8 * m + 4 by ring] at h2
      simp [h3'] at h2
      specialize h1 (2 * m + 1)
      have r: Odd (2 * m + 1) := by
        rw [odd_iff_exists_bit1]
        use m
      simp [r] at h1
      simp [h1] at h2

    -- then 8m-2 is not blue
    have u: ¬ 8 * m - 2 ∈ blue := by
      by_contra! u
      specialize h3 (8 * m - 2)
      have j: 8 * m - 2 > 0 := by
        omega
      simp [j] at h3
      simp [u] at h3
      rw [show 8 * m - 2 + 2 = 8 * m by omega] at h3
      rw [show 8 * m - 2 + 4 = 8 * m + 2 by omega] at h3
      rcases h3 with h3 | h3
      .
        tauto
      .
        tauto

    -- then 8m is not blue
    have v: ¬ 8 * m - 4 ∈ blue := by
      by_contra! v
      specialize h3 (8 * m - 4)
      have j: 8 * m - 4 > 0 := by
        omega
      simp [j] at h3
      simp [v] at h3
      rw [show 8 * m - 4 + 2 = 8 * m - 2 by omega] at h3
      rw [show 8 * m - 4 + 4 = 8 * m by omega] at h3
      rcases h3 with h3 | h3
      .
        tauto
      .
        tauto

    -- then 2 * m - 1 is not blue
    have w: ¬ 2 * m - 1 ∈ blue := by
      by_contra! w
      specialize h2 (2 * m - 1)
      have j: 2 * m - 1 > 0 := by
        omega
      simp [j] at h2
      simp [w] at h2
      rw [show 4 * (2 * m - 1) = 8 * m - 4 by omega] at h2
      tauto

    -- then we arrive at a contradiction
    absurd w
    specialize h1 (2 * m - 1)
    have r: Odd (2 * m - 1) := by
      rw [odd_iff_exists_bit1]
      use (m - 1)
      omega
    simp [r] at h1
    exact h1
    