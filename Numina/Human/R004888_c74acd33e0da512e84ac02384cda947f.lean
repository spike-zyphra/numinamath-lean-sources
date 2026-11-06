import Mathlib

/- $\mathbb{N}^{*}$ désigne l'ensemble des entiers supérieurs ou égaux à un. Trouver toutes les applications $\mathrm{f}: \mathbb{N}^{*} \rightarrow \mathbb{N}^{*}$ vérifiant :
i) quel que soit $n$ appartenant à $\mathbb{N}^{*}, f(n+f(n))=f(n)$
ii) $f(2013)=1$. -/
theorem number_theory_604444{f: PNat → PNat}:
  ((∀n, f (n + f n) = f n) ∧ (f 2013 = 1)) ↔
  (f = fun _ => 1) := by
  constructor
  · rintro ⟨hf, f2013⟩
    -- if f(a) = 1, then f (a + f(a)) = f (a + 1) = f(a) = 1.
    -- f(a') = 1 holds for all a' ≥ a.
    have h1{a:PNat}(hfa: f a = 1):
      ∀a', a' ≥ a → f a' = 1 := by
      intro a' ha'
      induction' a' using PNat.recOn with a' ih
      · by_cases ha: a = 1
        · nth_rw 1 [← ha, hfa]
        · have: a = 1 := PNat.le_one_iff.mp ha'
          simp [this] at ha
      by_cases ha1: a' < a
      · have: a'+1 = a := by
          apply le_antisymm ?_ ha'
          exact ha1
        rw [this, hfa]
      · push_neg at ha1
        -- by inductive hypothesis, fa' = 1.
        nth_rw 1 [← ih ha1]
        -- by problem statement, f (n+fn) = f(n)
        rw [hf a', ih ha1]
    -- if f(b+1) = 1, then we also have f (b) = 1
    have h2{b:PNat}(hfb: f (b+1) = 1):
      f b = 1 := by
      -- by problem statement, f (b) = f (b + f(b))
      rw [← hf b]
      -- from h1, it suffices to prove b+fb ≥ b+1
      refine h1 hfb _ ?_
      -- which trivially follows from fb ≥ 1(range of f is PNat)
      simp
    -- induction backwards
    have h3{b n:PNat}(hfb: f (b+n) = 1):
      f b = 1 := by
      induction' n using PNat.recOn with n ih
      · apply h2 hfb
      · rw [← add_assoc] at hfb
        apply ih
        apply h2 hfb
    -- therefore f1 =1
    have: f 1 = 1 := by
      have: (2013:PNat) = 1 + 2012 := rfl
      rw [this] at f2013
      apply h3 f2013
    -- done.
    funext n
    apply h1 this _ (by simp)
  · -- verification
    intro hf
    simp [hf]