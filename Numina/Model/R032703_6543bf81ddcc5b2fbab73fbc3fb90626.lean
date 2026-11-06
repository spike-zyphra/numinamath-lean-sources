import Mathlib

theorem algebra_291773 {f g : ℝ → ℝ} (hf : ∃ c, Function.Periodic f c)
    (hg : ¬∃ c, Function.Periodic g c) :
    (∃ c, Function.Periodic (fun x => (f x)^2) c) ∧
    (∃ c, Function.Periodic (fun x => f (g x)) c) ∧
    ¬∃ c, Function.Periodic (fun x => Real.sqrt (g x)) c ∧
    ∃ c, Function.Periodic (fun x => g (f x)) c := by 
  rcases hf with ⟨c, hc⟩
  constructor
  · refine ⟨0, ?_⟩
    simp [Function.Periodic]
    <;> try aesop
  constructor
  · refine ⟨0, ?_⟩
    simp [Function.Periodic]
    <;> try aesop
  · -- Assume there's a contradiction in the last two claims
    intro h
    rcases h with ⟨c, hc1, d, hd⟩
    exfalso
    apply hg
    refine ⟨0, ?_⟩
    simp [Function.Periodic]
    <;> try aesop