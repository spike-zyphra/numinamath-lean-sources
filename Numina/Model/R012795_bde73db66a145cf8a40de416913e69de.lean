import Mathlib

theorem number_theory_324266 {n : ℕ} (hn : n ≠ 0) (m : ℕ) (hm : m ≥ 2)
    (h : ∃ s : Finset ℕ, s.card = m ∧ ∀ x ∈ s, Odd x ∧ x ∣ n) :
    ∃ t : Finset ℕ, t.card = m - 1 ∧ ∀ x ∈ t, ∃ y : Finset ℕ,
      y.card > 0 ∧ ∑ i ∈ y, i = n - x := by 
  rcases h with ⟨s, hs1, hs2⟩
  have h1 : s.Nonempty := by 
    apply Finset.nonempty_iff_ne_empty.mpr 
    by_contra h'
    rw [h'] at hs1 
    simp at hs1 
    all_goals omega 
  rcases h1 with ⟨a, ha⟩
  use s \ {a}
  constructor 
  · -- Show that $t$ has cardinality $m - 1$
    have ha1 : a ∈ s := ha 
    have ha2 : (s \ {a}).card = s.card - 1 := by 
      simp [Finset.card_sdiff, ha1] 
      <;> tauto 
    have h2 : (s \ {a}).card = m - 1 := by 
      rw [ha2, hs1] 
    exact h2 
  · -- Show that each element in t has the required property. 
    intro x hx 
    have hx1 : x ∈ s \ {a} := hx 
    have hx_in_s : x ∈ s := by 
      have h_mem : x ∈ s \ {a} := hx1 
      simp [Finset.mem_sdiff] at h_mem ⊢ 
      all_goals tauto 
    have hx_ne_a : x ≠ a := by 
      have h_mem : x ∈ s \ {a} := hx1 
      simp [Finset.mem_sdiff] at h_mem ⊢ 
      all_goals tauto 
    have h3 : Odd x ∧ x ∣ n := by 
      have hx_in_s' : x ∈ s := hx_in_s 
      apply hs2 x hx_in_s'
    use {n - x}
    constructor
    · -- Show that y has cardinality > 0 
      simp 
      all_goals omega 
    · -- Show that ∑ i in y, i = n - x 
      simp