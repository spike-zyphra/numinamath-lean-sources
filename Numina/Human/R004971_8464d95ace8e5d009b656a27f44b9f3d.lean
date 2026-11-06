import Mathlib

/-
A set A of integers is called admissible if it satisfies the following property:
For any x,y∈A (where x=y is allowed), x^2 +kxy+y^2 ∈A holds for every integer k
Determine all pairs (m,n) of nonzero integers for which the only admissible set containing both m and n is the set ℤ of all integers.-/

theorem number_theory_604859: {(m, n): ℤ × ℤ | m ≠ 0 ∧ n ≠ 0 ∧ ∀ A: Set ℤ, m ∈ A ∧ n ∈ A ∧
  (∀ x ∈ A, ∀ y ∈ A, ∀ k: ℤ, x^2 + k * x * y + y^2 ∈ A) → ∀ x: ℤ, x ∈ A} =
  {(m, n): ℤ × ℤ | m ≠ 0 ∧ n ≠ 0 ∧ m.gcd n = 1} := by

  ext ⟨m, n⟩
  simp only [Set.mem_setOf_eq]
  constructor

  -- the forward direction: show that if the set is admissible, then m and n are coprime
  .
    intro h
    rcases h with ⟨nem, nen, h⟩
    simp [nem,nen]
    by_contra! o
    set d:= m.gcd n
    have dm: ↑d ∣ m := by
      apply Int.gcd_dvd_left
    have dn: ↑d ∣ n := by
      apply Int.gcd_dvd_right
    have ld: 0 < d := by
      simp [d]
      apply Int.gcd_pos_of_ne_zero_left
      exact nem
    replace ld: 2 ≤ d := by omega
    let B: Set ℤ := {z: ℤ | ↑d ∣ z}

    -- note that B is admissible, but not ℤ
    specialize h B

    have c: ∀ n: ℤ, n ∈ B := by -- this is where the contradiction comes from
      apply h
      clear h
      have vm: m ∈ B := by
        simp [B]
        exact dm
      have vn: n ∈ B := by
        simp [B]
        exact dn
      simp [vm, vn]
      intro x hx y hy
      intro k
      simp [B]
      simp [B] at hx hy
      have o1: ↑d ∣ x ^ 2 := by
        have o2: x ∣ x ^ 2 := by
          rw [show x ^ 2 = x * x by ring]
          simp
        apply dvd_trans hx o2
      have o2: ↑d ∣ y ^ 2 := by
        have o3: y ∣ y ^ 2 := by
          rw [show y ^ 2 = y * y by ring]
          simp
        apply dvd_trans hy o3
      have o3: ↑d ∣ k * x * y := by
        have o4: y ∣ k * x * y:= by
          simp
        apply dvd_trans hy o4
      apply dvd_add
      apply dvd_add
      exact o1
      exact o3
      exact o2
    -- but 1 is not in B
    specialize c 1
    simp [B] at c
    norm_cast at c
    apply Nat.le_of_dvd at c
    omega
    norm_num

  -- the backward direction: show that if m and n are coprime, then the set is admissible
  .
    intro h
    rcases h with ⟨nem, nen, hd⟩
    simp [nem,nen]
    intro A hm hn
    intro h
    intro q

    -- it suffices to show that 1 ∈ A
    have g: 1 ∈ A := by
      rw [← Int.isCoprime_iff_gcd_eq_one] at hd
      replace hd: IsCoprime (m ^ 2) (n ^ 2) := by
        apply IsCoprime.pow
        exact hd
      rw [Int.isCoprime_iff_gcd_eq_one] at hd
      zify at hd
      have o: ↑((m ^ 2).gcd (n ^ 2)) = gcd (m ^ 2) (n ^ 2) := by
        norm_cast
      replace hd: gcd (m ^ 2) (n ^ 2) ∣ 1 := by
        rw [← o]
        rw [hd]
      rw [gcd_dvd_iff_exists] at hd
      obtain ⟨r, s, f⟩ := hd  -- use coprime property
      rw [show m ^ 2 * r + n ^ 2 * s = r * (m ^ 2) + s * (n ^ 2) by ring] at f
      replace f: 1 = (r * (m ^ 2) + s * (n ^ 2)) ^ 2 := by
        rw [← f]
        norm_num
      rw [f]
      -- we show multiple of m ^ 2 and n ^ 2 are in A
      have am: r * (m ^ 2) ∈ A := by
        specialize h m hm m hm (r - 2)
        ring_nf at h
        rw [show r * m ^ 2 = m ^ 2 * r by ring]
        exact h

      have an: s * (n ^ 2) ∈ A := by
        specialize h n hn n hn (s - 2)
        ring_nf at h
        rw [show s * n ^ 2 = n ^ 2 * s by ring]
        exact h

      -- then use the fact x y in A then (x + y) ^ 2 in A
      specialize h (r * (m ^ 2)) am (s * (n ^ 2)) an 2
      ring_nf
      ring_nf at h
      exact h

    specialize h 1 g 1 g (q - 2)
    norm_num at h
    rw [show 1 + (q - 2) + 1 = q by omega] at h
    exact h