import Mathlib

open Function

def f (S T : Type) : Prop := ∃ f : T → S, Surjective f ∧ ¬∃ f : S → T, Surjective f

theorem other_5254 {S T U : Type} (hST : f S T) (hTU : f T U) : f S U := by
  rcases hST with ⟨f_s_t, hf_s_t, hf_not_s_t⟩
  rcases hTU with ⟨f_t_u, hf_t_u, hf_not_t_u⟩
  use f_s_t ∘ f_t_u
  constructor
  · -- Show that $f$ is surjective
    intro s
    have h1 : ∃ t, f_s_t t = s := hf_s_t s
    rcases h1 with ⟨t, hf_s_tsur⟩
    have h2 : ∃ u, f_t_u u = t := hf_t_u t
    rcases h2 with ⟨u, hf_t_usur⟩
    exact ⟨u, by
      simp [hf_s_tsur, hf_t_usur]
      <;> try tauto
      <;> try simp_all
      <;> try tauto
    ⟩
  · -- Show no surjective function from $S$ to $U$
    intro h
    rcases h with ⟨g_s_u, hsurj⟩
    have hT_s_U : ∃ f : T → U, Surjective f := ⟨g_s_u ∘ f_s_t, by
      intro u
      have hsurj_s : ∃ s, g_s_u s = u := hsurj u
      rcases hsurj_s with ⟨s, hsurj_s⟩
      have hf_s_tsur : ∃ t, f_s_t t = s := hf_s_t s
      rcases hf_s_tsur with ⟨t, hf_s_tsur⟩
      exact ⟨t, by
        show g_s_u (f_s_t t) = u
        have h1 : f_s_t t = s := by
          exact hf_s_tsur
        rw [show f_s_t t = s by exact h1]
        exact hsurj_s
      ⟩
    ⟩
    have h' : ¬∃ f : T → U, Surjective f := hf_not_t_u
    obtain h' := h' hT_s_U
    contradiction