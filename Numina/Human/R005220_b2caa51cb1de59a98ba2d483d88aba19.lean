import Mathlib

open Pointwise Finset Classical

/- For any interger set S, if S ≠ ∅ and S = S + 1, then S = ℤ -/
lemma eq_top_of_one_shity {S : Set ℤ} (h : S = S + 1) (hne : S.Nonempty) : S = ⊤ := by
  apply subset_antisymm
  · exact fun ⦃a⦄ a ↦ trivial
  · obtain ⟨a, ha⟩ := hne
    intro x hx
    refine Int.inductionOn' x a ha ?_ ?_
    · intro k hak hkS
      rw [h]
      use k, hkS, 1
      simp
    · intro k hka hkS
      rw [h] at hkS
      obtain ⟨m, hm, b, hb, h⟩ := hkS
      simp at h hb
      rw [hb] at h
      rw [←h]
      simp [hm]

/- Prove that S = S + {v ^ 2 - u ^ 2} if S satisfies the second property. -/
lemma exists_shifty {S : Set ℤ} (h : ∀ x y, x ∈ S → y ∈ S → x ^ 2 - y ∈ S) {u v : ℤ} (hu : u ∈ S) (hv : v ∈ S) :
    S = S + {(v ^ 2 - u ^ 2)} := by
  ext x
  constructor <;> intro hx
  · have h₁ : v ^ 2 - x ∈ S := by
      apply h v x hv hx
    have h₂ : u ^ 2 - (v ^ 2 - x) ∈ S := by
      apply h u (v ^ 2 - x) hu h₁
    use u ^ 2 - (v ^ 2 - x), h₂, v ^ 2 - u ^ 2
    simp
  · obtain ⟨a, ha, b, hb, heq⟩ := hx
    simp at heq hb
    rw [hb] at heq
    rw [←heq]
    have h₁ : u ^ 2 - a ∈ S := by
      apply h u a hu ha
    have h₂ : v ^ 2 - (u ^ 2 - a) ∈ S := by
      apply h v (u ^ 2 - a) hv h₁
    ring_nf at h₂ ⊢
    exact h₂

/- Prove that if S = S + {d}, then S = S + {k * d} -/
lemma mul_shifty {S : Set ℤ} {d : ℤ} (hS : S = S + {d}) (k : ℤ) : S = S + {k * d} := by
  ext x
  simp at hS ⊢
  induction k using Int.induction_on generalizing x
  · simp
  · rename_i k ih
    constructor <;> intro hx
    · apply ih x |>.mp at hx
      rw [hS] at hx
      simp at hx
      ring_nf at hx ⊢
      exact hx
    · rw [hS]
      simp
      apply ih _ |>.mpr
      ring_nf at hx ⊢
      exact hx
  · rename_i k ih
    constructor <;> intro hx
    · apply ih x |>.mp at hx
      rw [hS]
      simp
      ring_nf at hx ⊢
      exact hx
    · rw [hS] at hx
      simp at hx
      apply ih _ |>.mpr
      ring_nf at hx ⊢
      exact hx

/- Prove that S = S + {d₁ + d₂} if S = S + {d₁} and S = S + {d₂} -/
lemma add_shifty {S : Set ℤ} {d₁ d₂ : ℤ} (hS : S = S + {d₁}) (hS' : S = S + {d₂}) :
    S = S + {d₁ + d₂} := by
  ext x
  simp at hS hS' ⊢
  constructor <;> intro hx
  · rw [hS] at hx
    simp at hx
    rw [hS'] at hx
    simp at hx
    ring_nf at hx ⊢
    exact hx
  · rw [hS]
    simp
    rw [hS']
    simp
    ring_nf at hx ⊢
    exact hx

/- Prove that if S = S + {d₁} and S = S + {d₂}, then S = S + {gcd d₁ d₂} according to the berzout's lemma -/
lemma gcd_shifty {S : Set ℤ} {d₁ d₂ : ℤ} (hd₁ : S = S + {d₁}) (hd₂ : S = S + {d₂}) :
    S = S + {↑(Int.gcd d₁ d₂)} := by
  obtain ⟨s, t, h⟩ := exists_gcd_eq_mul_add_mul d₁ d₂
  have : GCDMonoid.gcd d₁ d₂ = Int.gcd d₁ d₂ := by
    exact rfl
  rw [←this, h]
  apply add_shifty
  · rw [mul_comm]
    apply mul_shifty
    exact hd₁
  · rw [mul_comm]
    apply mul_shifty
    exact hd₂

/- Consider all k > 0 such that S = S + {k}, we show that they are in dℤ for some d > 0 and S = S {d} -/
lemma eq_mul_int_of_shifty {S : Set ℤ} (hS : ∃ d > 0, S = S + {d}) : ∃ d > 0, S = S + {d} ∧ ∀ k > 0, S = S + {k} → d ∣ k := by
  by_contra h
  push_neg at h
  -- By contradiction, if such d does not exist, we take the infimum of all d > 0 such that S = S + {d}.
  let shifty := {d | d > 0 ∧ S = S + {d}}
  have : shifty.Nonempty := by
    obtain ⟨d, hd, hS'⟩ := hS
    use d, hd, hS'
  let d := sInf shifty
  have hbdd : BddBelow shifty := by
    use 0
    intro x hx
    simp [shifty] at hx
    apply le_of_lt hx.1
  have hd : d ∈ shifty := by
    refine Int.csInf_mem hS hbdd
  simp only [shifty] at hd
  -- Then there exists k > 0 such that S = S + {k} and ¬ d ∣ k.
  have hd' : ∀ k ∈ shifty, k ≥ d := by
    intro k hk
    apply csInf_le hbdd hk
  obtain ⟨k, hkpos, hkS, hkdvd⟩ := h d hd.1 hd.2
  let m := Int.gcd d k
  have hm : ↑m ∈ shifty := by
    simp [shifty, m]
    constructor
    · apply Int.gcd_pos_of_ne_zero_left
      apply ne_of_gt hd.1
    · obtain h := gcd_shifty hd.2 hkS
      simp at h
      exact h
  apply hd' at hm
  -- However, we know that S = S + {gcd d k} and hence gcd d k ≥ d.
  -- Therefore, d = gcd d k and d ∣ k, which is a contradiction.
  have hm : m = d := by
    apply le_antisymm
    · have : ↑m ∣ d := by
        exact Int.gcd_dvd_left
      apply Int.le_of_dvd hd.1 this
    · exact hm
  have : d ∣ k := by
    rw [←hm]
    exact Int.gcd_dvd_right
  contradiction

/- If (a ^ 2 - a) ^ 2 ≡ a [ZMOD p], then p ∣ a ∨ p ∣ 2 -/
lemma dichotomy_of_ModEq_of_dvd {a d : ℤ} (h : (a ^ 2 - a) ^ 2 ≡ a ^ 2 [ZMOD d]) {p : ℕ} (hdvd : ↑p ∣ d) (hp : Nat.Prime p) :
    ↑p ∣ a ∨ ↑p ∣ (a - 2) := by
  have : a ^ 3 * (a - 2) ≡ 0 [ZMOD p] := by
    trans (a ^ 2 - a) ^ 2 - a ^ 2
    · congr 1
      ring_nf
    trans a ^ 2 - a ^ 2
    · apply Int.ModEq.sub ?_ rfl
      apply Int.ModEq.of_dvd hdvd h
    · simp
  apply Int.modEq_iff_dvd.mp at this
  simp at this
  apply Int.Prime.dvd_mul' hp at this
  rcases this with h | h
  · left
    exact Int.Prime.dvd_pow' hp h
  · right
    exact h

/- Let $S \subseteq \mathbb{Z}$ be such that: (a) there exist $a, b \in S$ with $\operatorname{gcd}(a, b)=\operatorname{gcd}(a-2, b-2)=1$; (b) if $x$ and $y$ are elements of $S$ (possibly equal), then $x^{2}-y$ also belongs to $S$. Prove that $S=\mathbb{Z}$. -/
theorem number_theory_606329 {S : Set ℤ} (h1 : ∃ a b, a ∈ S ∧ b ∈ S ∧ Int.gcd a b = 1 ∧ Int.gcd (a - 2) (b - 2) = 1)
    (h2 : ∀ x y, x ∈ S → y ∈ S → x ^ 2 - y ∈ S) : S = ⊤ := by

  -- S is not empty
  have hne : S.Nonempty := by
    obtain ⟨a, b, ha, hb, hga, hgb⟩ := h1
    use a

  -- By our lemma, it suffices to show that S = S + 1
  apply eq_top_of_one_shity ?_  hne

  obtain ⟨a, b, ha, hb, hga, hgb⟩ := h1

  -- We first show that there exists a positive integer d such that S = S + {d}
  have : ∃ d > 0, S = S + {d} := by
    -- We know that a and b are two elements of S such that gcd(a, b) = 1 and gcd(a - 2, b - 2) = 1.
    -- By our lemma,  S = S + a ^ 2 - b ^ 2.
    by_cases hab : a ^ 2 < b ^ 2
    · -- If a ^ 2 < b ^ 2, then S = S + {b ^ 2 - a ^ 2}.
      obtain h := exists_shifty h2 ha hb
      use b ^ 2 - a ^ 2
      constructor
      · simp
        exact hab
      · exact h
    · simp at hab
      rcases lt_or_eq_of_le hab with hab | hab
      · -- If a ^ 2 > b ^ 2, then S = S + {a ^ 2 - b ^ 2}.
        obtain h := exists_shifty h2 hb ha
        use a ^ 2 - b ^ 2
        constructor
        · simp
          exact hab
        · exact h
      · -- If a ^ 2 = b ^ 2, then we have two cases:
        have : (b - a) * (b + a) = 0 := by
          apply sub_eq_zero.mpr at hab
          rw [←hab]
          ring
        simp at this
        rcases this with h | h
        · -- case 1 : a = b
          -- We obtain that a = b = 1, then 0 = a ^ 2 - b ∈ S.
          -- We have S = S + 1 ^ 2 - 0 ^ 2
          apply sub_eq_zero.mp at h
          simp [h] at hga hgb
          have : a = -1 ∨ a = 1 := by
            exact Or.symm ((fun {a b} ↦ Int.natAbs_eq_natAbs_iff.mp) hga)
          rcases this with h' | h'
          · simp [h'] at hgb
          · simp [h'] at ha
            obtain h0 : 0 ∈ S := by
              apply h2 1 1 ha ha
            obtain h := exists_shifty h2 h0 ha
            use 1
            constructor
            · simp
            · exact h
        · -- case 2 : a ≠ b
          -- We have b = -1 or b = 1 and 0 ∈ S.
          -- Similarly, we obtain that S = S + 1 ^ 2 - 0 ^ 2
          have : a = -b := by exact Eq.symm (Int.neg_eq_of_add_eq_zero h)
          simp [this] at hga hgb
          have : b = -1 ∨ b = 1 := by
            exact Or.symm ((fun {a b} ↦ Int.natAbs_eq_natAbs_iff.mp) hga)
          rcases this with h | h
          · simp [h] at this hb
            simp [this] at ha
            have : 0 ∈ S := by
              apply h2 1 1 ha ha
            obtain h := exists_shifty h2 this ha
            use 1
            constructor
            · simp
            · exact h
          · rw [h] at hb
            have : 0 ∈ S := by
              apply h2 1 1 hb hb
            obtain h := exists_shifty h2 this hb
            use 1
            constructor
            · simp
            · exact h
  -- Then we prove that all positive integers such that S = S + {k} for some k > 0 are multiples of d for some d > 0 and S = S + {d}
  obtain ⟨d, hdpos, hd, hdvd⟩ := eq_mul_int_of_shifty this
  by_cases hd_eq_one : d = 1
  · -- If d = 1, then S = S + {1} and hence the result follows
    rw [hd_eq_one] at hd
    nth_rw 1 [hd]
    congr
  · -- Otherwise, we claim that ∀ x ∈ S, x ^ 2 ≡ a ^ 2 [ZMOD d].
    have claim : ∀ x ∈ S, x ^ 2 ≡ a ^ 2 [ZMOD d] := by
      intro x hx
      clear hga hgb
      wlog hxa : x ^ 2 > a ^ 2 generalizing x a with H
      · have : x ^ 2 ≤ a ^ 2 := by
          exact Int.not_lt.mp hxa
        rcases lt_or_eq_of_le this with hxa | hxa
        · obtain H := H x hx a ha hxa
          exact id (Int.ModEq.symm H)
        · simp [hxa]
      · have : S = S + {x ^ 2 - a ^ 2} := by
          apply exists_shifty h2 ha hx
        have hpos : x ^ 2 - a ^ 2 > 0 := by
          exact Int.sub_pos_of_lt hxa
        apply hdvd _ hpos at this
        exact Int.ModEq.symm ((fun {n a b} ↦ Int.modEq_iff_dvd.mpr) this)
    -- Let a and b be the two elements of S such that gcd(a, b) = 1 and gcd(a - 2, b - 2) = 1.
    -- By our claim, we have that a ^ 2 ≡ b ^ 2 [ZMOD d].
    have h₁ : b ^ 2 ≡ a ^ 2 [ZMOD d] := by
      apply claim b hb
    -- and (a ^ 2 - a) ^ 2 ≡ a ^ 2 [ZMOD d] and (b ^ 2 - b) ^ 2 ≡ b ^ 2 [ZMOD d].
    have h₂ : (a ^ 2 - a) ^ 2 ≡ a ^ 2 [ZMOD d] := by
      apply claim (a ^ 2 - a)
      apply h2 a a ha ha
    have h₃ : (b ^ 2 - b) ^ 2 ≡ b ^ 2 [ZMOD d] := by
      trans a ^ 2
      · apply claim (b ^ 2 - b)
        apply h2 b b hb hb
      · exact id (Int.ModEq.symm h₁)

    -- Consider a prime p such that p ∣ d since d > 1.
    obtain ⟨p, hp, hpdvd⟩ : ∃ p, Prime p ∧ p ∣ d := by
      apply Int.exists_prime_and_dvd
      by_contra hd
      have : d = -1 ∨ d = 1 := by exact Or.symm ((fun {a b} ↦ Int.natAbs_eq_natAbs_iff.mp) hd)
      rcases this with h | h
      · simp [h] at hdpos
      · simp [h] at hd_eq_one
    let p := p.natAbs
    have hp : Nat.Prime p := by
      exact Int.prime_iff_natAbs_prime.mp hp
    have hpdvd : ↑p ∣ d := by
      exact Int.natAbs_dvd.mpr hpdvd
    -- Since (a ^ 2 - a) ^ 2 ≡ a ^ 2 [ZMOD d], we have that p ∣ a ∨ p ∣ (a - 2).
    obtain h₂ := dichotomy_of_ModEq_of_dvd h₂ hpdvd hp
    -- Similarly, since (b ^ 2 - b) ^ 2 ≡ b ^ 2 [ZMOD d], we have that p ∣ b ∨ p ∣ (b - 2).
    obtain h₃ := dichotomy_of_ModEq_of_dvd h₃ hpdvd hp
    have h₁ : b ^ 2 ≡ a ^ 2 [ZMOD p] := by
      apply Int.ModEq.of_dvd hpdvd h₁
    rcases h₂ with h₂ | h₂
    · -- If p ∣ a, then we also have that p ∣ a - 2.
      -- Therefore, p ∣ a.gcd b = 1, which is a contradiction.
      have h₁ : b ^ 2 ≡ 0 [ZMOD p] := by
        apply Int.ModEq.trans h₁
        apply Int.modEq_of_dvd
        simp
        rw [sq]
        exact Dvd.dvd.mul_right h₂ a
      apply Int.modEq_iff_dvd.mp at h₁
      simp at h₁
      have : ↑p ∣ b := by
        exact Int.Prime.dvd_pow' hp h₁
      have : ↑p ∣ a.gcd b := by
        apply GCDMonoid.dvd_gcd
        · exact Int.ofNat_dvd_left.mp h₂
        · exact Int.ofNat_dvd_left.mp this
      rw [hga] at this
      have : ¬ p ∣ 1 := by
        exact Nat.Prime.not_dvd_one hp
      contradiction
    · rcases h₃ with h₃ | h₃
      · -- If p ∣ b, then we also have that p ∣ a since a ^ 2 ≡ b ^ 2 [ZMOD p].
        -- Therefore, p ∣ a.gcd b = 1, which is a contradiction.
        have h₁ : 0 ≡ a ^ 2 [ZMOD p] := by
          apply Int.ModEq.trans ?_ h₁
          apply Int.modEq_of_dvd
          simp
          rw [sq]
          exact Dvd.dvd.mul_right h₃ b
        apply Int.modEq_iff_dvd.mp at h₁
        simp at h₁
        have : ↑p ∣ a := by
          exact Int.Prime.dvd_pow' hp h₁
        have : ↑p ∣ a.gcd b := by
          apply GCDMonoid.dvd_gcd
          · exact Int.ofNat_dvd_left.mp this
          · exact Int.ofNat_dvd_left.mp h₃
        rw [hga] at this
        have : ¬ p ∣ 1 := by
          exact Nat.Prime.not_dvd_one hp
        contradiction
      · -- Otherwise, it must be the case that p ∣ a - 2 and p ∣ b - 2.
        -- Therefore, p ∣ (a - 2).gcd (b - 2) = 1, which is a contradiction.
        have : ↑p ∣ (a - 2).gcd (b - 2) := by
          apply GCDMonoid.dvd_gcd
          · exact Int.ofNat_dvd_left.mp h₂
          · exact Int.ofNat_dvd_left.mp h₃
        rw [hgb] at this
        have : ¬ p ∣ 1 := by
          exact Nat.Prime.not_dvd_one hp
        contradiction
