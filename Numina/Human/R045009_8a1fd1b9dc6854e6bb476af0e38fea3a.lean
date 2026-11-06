import Mathlib

open Finset Function

theorem number_theory_609689 :
  #{n ∈ Icc 1 1000000 | n % 1000 > n % 1001} = 499500 := by

  let s1 := (range 1000).powersetCard 2

  -- there's 499500 way to choose two numbers from 0 to 999
  have h1: #s1 = 499500 := by
    simp [s1, Finset.card_powersetCard, Nat.choose_two_right]

  let s2 := ((range 1000) ×ˢ (range 1001)).filter (λ (a, b) => a > b)

  -- each two numbers from 0 to 999 can be represented as a pair (a, b) where a ∈ range 1000, b ∈ range 1001, a > b
  have h2: #s2 = #s1 := by
    unfold s2 s1

    -- prove by build bijection
    apply card_nbij (λ (a, b) => {a, b})
    . intro x
      simp
      intro h₁ h₂ h₃
      have h₄: x.2 ≤ 999 := by linarith
      constructor
      . simp [Finset.insert_subset_iff]
        exact ⟨h₁, by linarith⟩
      . apply Finset.card_pair
        linarith
    . simp [Set.InjOn]
      intro a b ha hb hab
      intro a' b' ha' hb' hab'
      intro heq
      simp [← Finset.coe_eq_pair, Set.pair_eq_pair_iff] at heq
      rcases heq with heq | heq
      . exact heq
      . linarith
    . simp [Set.SurjOn, Set.subset_def]
      intro x hx1 hx2
      rw [card_eq_two] at hx2
      let ⟨a, b, hab⟩ := hx2
      have ha: a ∈ range 1000 := by
        apply Finset.mem_of_subset hx1
        simp [hab.2]
      have hb: b ∈ range 1000 := by
        apply Finset.mem_of_subset hx1
        simp [hab.2]
      rw [mem_range] at ha hb
      by_cases hl: a < b
      . have h₁ : ((b < 1000 ∧ a < 1001) ∧ a < b) := by
          constructor <;> try constructor
          all_goals linarith
        exact ⟨b, a, ⟨h₁, by simp [hab, pair_comm]⟩ ⟩
      . have h₁ : b < a := by
          apply lt_of_le_of_ne
          linarith
          simp [ne_comm, hab.1]

        have h₂ : ((a < 1000 ∧ b < 1001) ∧ b < a) := by
          constructor <;> try constructor
          all_goals linarith
        exact ⟨a, b, ⟨h₂, by simp [hab]⟩⟩

  -- by chinese remainder theorem, there's exactly one n for each pair such as n ≡ a (mod 1000) and n ≡ b (mod 1001)
  let s3 := {n ∈ range 1001000 | n % 1000 > n % 1001}
  have h3: #s3 = #s2 := by
    unfold s2 s3
    apply card_nbij (λ n => (n % 1000, n % 1001))
    . intro a
      simp
      intro h₁ h₂
      constructor <;> try constructor
      simp [Nat.mod_lt]
      simp [Nat.mod_lt]
      exact h₂
    . simp [Set.InjOn]
      intro x h₁ h₂
      intro x2 h₃ h₄ h₅ h₆
      have h1: x % 1001000 = x2 % 1001000 := by
        rw [Nat.mod_eq_of_modEq] ; all_goals try simp [Nat.mod_lt]
        rw [Nat.mod_eq_of_modEq] ; all_goals try linarith
        rw [show 1001000 = 1000*1001 by norm_num]
        rw [← Nat.modEq_and_modEq_iff_modEq_mul]
        constructor
        . simp [Nat.ModEq, h₅]
        . simp [Nat.ModEq, h₆]
        . norm_num
      have h2: x % 1001000 = x := by
        apply Nat.mod_eq_of_lt
        exact h₁
      have h3: x2 % 1001000 = x2 := by
        apply Nat.mod_eq_of_lt
        exact h₃
      rw [h2, h3] at h1
      exact h1
    . simp [Set.SurjOn, Set.subset_def]
      intro a b
      intro ha hb hba
      let x := (b + (1000 + a - b)*1001) % 1001000
      use x
      have h1: x % 1001 = b := by
        omega
      have h2: x % 1000 = a := by
        omega
      simp [x, Nat.mod_lt, h1, h2, hba]

  let s4 :={n ∈ Ico 1 1000001 | n % 1000 > n % 1001}

  -- split range 1001000 into three parts: Ico 0 1, Ico 1 1000001, Ico 1000001 1001000
  have h4: #s4 = #s3 := by
    unfold s3 s4
    rw [range_eq_Ico, ← Ico_union_Ico_eq_Ico (by norm_num : (0 : ℕ) ≤ 1) (by norm_num : (1 : ℕ) ≤ 1001000),
      ← Ico_union_Ico_eq_Ico (by norm_num : (1 : ℕ) ≤ 1000001) (by norm_num : (1000001 : ℕ) ≤ 1001000)]
    have h5: filter (fun n => n % 1001 < n % 1000) (Ico 1000001 1001000) = ∅ := by
      rw [filter_eq_empty_iff]
      intro x hx
      rw [mem_Ico] at hx
      have h6: x % 1001 > x % 1000 := by omega
      linarith

    simp [Finset.filter_union, Finset.filter_singleton, Nat.mod_eq_of_lt]
    norm_num [h5]


  rw [h3, h2, h1] at h4
  exact h4
