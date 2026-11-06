import Mathlib

theorem algebra_12654 {f g : ℝ → ℝ} (hf : f = fun x => x + g x)
    (hg : ∀ x, g (x + 2) = g x) (hmax : IsGreatest (Set.image f (Set.Ico 2 4)) 1) :
    IsGreatest (Set.image f (Set.Ico 10 12)) 9 := by
  have h1 : ∀ x, g (x + 2) = g x := hg
  have h2 : 1 ∈ Set.image f (Set.Ico 2 4) := by
    exact hmax.1
  rcases h2 with ⟨c, hc, heq⟩
  have hc1 : 2 ≤ c := by 
    have h1 : c ∈ Set.Ico (2 : ℝ) (4 : ℝ) := hc
    exact h1.1
  have hc2 : c < 4 := by 
    have h1 : c ∈ Set.Ico (2 : ℝ) (4 : ℝ) := hc
    exact h1.2
  have h3 : 9 ∈ Set.image f (Set.Ico 10 12) := by
    use c + 8
    constructor
    · -- Show that c + 8 is in [10, 12)
      constructor
      · -- Show 10 ≤ c + 8
        linarith
      · -- Show c + 8 < 12
        linarith
    · -- Show f (c + 8) = 9
      have eq1 : f (c + 8) = (c + 8) + g (c + 8) := by
        rw [hf]
      have eq2 : g (c + 8) = g c := by
        have h1 : g (c + 2) = g c := by
          apply hg
        have h2 : g (c + 4) = g c := by
          calc
            g (c + 4) = g ((c + 2) + 2) := by ring_nf
            _ = g (c + 2) := by rw [hg]
            _ = g c := by rw [h1]
        have h3 : g (c + 6) = g c := by
          calc
            g (c + 6) = g ((c + 4) + 2) := by ring_nf
            _ = g (c + 4) := by rw [hg]
            _ = g c := by rw [h2]
        have h4 : g (c + 8) = g c := by
          calc
            g (c + 8) = g ((c + 6) + 2) := by ring_nf
            _ = g (c + 6) := by rw [hg]
            _ = g c := by rw [h3]
        exact h4
      have eq3 : (c + 8) + g c = 9 := by
        have eq4 : c + g c = 1 := by
          have heq1 : f c = 1 := by linarith [heq]
          have eq5 : f c = c + g c := by
            rw [hf]
          linarith
        linarith
      rw [eq1, eq2]
      linarith
  have h4 : ∀ y ∈ Set.image f (Set.Ico 10 12), y ≤ 9 := by
    intro y hy
    rcases hy with ⟨x, hx, heq⟩
    have hx1 : 10 ≤ x := by 
      have h1 : x ∈ Set.Ico (10 : ℝ) (12 : ℝ) := hx
      exact h1.1
    have hx2 : x < 12 := by 
      have h1 : x ∈ Set.Ico (10 : ℝ) (12 : ℝ) := hx
      exact h1.2
    have eq1 : f x = x + g x := by 
      rw [hf]
    have eq2 : g x = g (x - 8) := by
      have h4 : g ((x - 8) + 8) = g (x - 8) := by
        have h11 : g ((x - 8) + 2) = g (x - 8) := by
          apply hg
        have h12 : g ((x - 8) + 4) = g (x - 8) := by
          calc 
            g ((x - 8) + 4) = g (( (x - 8) + 2 ) + 2) := by ring_nf
            _ = g ((x - 8) + 2) := by rw [hg]
            _ = g (x - 8) := by rw [h11]
        have h13 : g ((x - 8) + 6) = g (x - 8) := by
          calc 
            g ((x - 8) + 6) = g (( (x - 8) + 4 ) + 2) := by ring_nf
            _ = g ((x - 8) + 4) := by rw [hg]
            _ = g (x - 8) := by rw [h12]
        have h14 : g ((x - 8) + 8) = g (x - 8) := by
          calc 
            g ((x - 8) + 8) = g (( (x - 8) + 6 ) + 2) := by ring_nf
            _ = g ((x - 8) + 6) := by rw [hg]
            _ = g (x - 8) := by rw [h13]
        exact h14
      have h4' : (x - 8) + 8 = x := by ring
      rw [h4'] at h4
      linarith
    have eq3 : f x = f (x - 8) + 8 := by
      have eq4 : f x = x + g x := by 
        rw [hf]
      have eq5 : f (x - 8) = (x - 8) + g (x - 8) := by
        rw [hf]
      rw [eq4, eq2]
      linarith [eq5]
    have hx0_in : x - 8 ∈ Set.Ico 2 4 := by
      constructor
      · -- Show 2 ≤ x - 8
        linarith
      · -- Show x - 8 < 4
        linarith
    have hx0_image : f (x - 8) ∈ Set.image f (Set.Ico 2 4) := by
      refine' ⟨x - 8, hx0_in, rfl⟩
    have hx0_le : f (x - 8) ≤ 1 := by 
      have h1 : IsGreatest (Set.image f (Set.Ico 2 4)) 1 := hmax
      have h2 : f (x - 8) ∈ Set.image f (Set.Ico 2 4) := hx0_image
      have h3 : f (x - 8) ≤ 1 := by 
        apply h1.2
        exact h2
      linarith
    linarith [eq3, hx0_le]
  constructor
  · -- Show 9 is in the image
    exact h3
  · -- Show no element greater than 9 is in the image
    intro y hy
    have h5 : ∀ y ∈ Set.image f (Set.Ico 10 12), y ≤ 9 := h4
    specialize h5 y hy
    linarith