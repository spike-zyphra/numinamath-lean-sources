import Mathlib

/- Vind alle functies $f: \mathbb{Z}_{>0} \rightarrow \mathbb{Z}_{>0}$ waarvoor geldt dat $f(n) \mid f(m)-n$ dan en slechts dan als $n \mid m$ voor alle natuurlijke getallen $m$ en $n$. -/
theorem number_theory_605203 (f : ℤ → ℤ) (hf: ∀n:ℤ, 1≤ n → 1 ≤ f n):
  (∀ n≥1, ∀ m≥ 1, (f n ∣ f m - n) ↔ (n ∣ m)) ↔ (∀ n≥1, f n = n) := by 

    constructor

    --From left to right.
    intro h
    
    --We prove it by induction. 
    --First we have f n ∣ n by using the assumption.
    have cla1: ∀ n ≥ 1, f n ∣ n := by 
      intro n hn
      specialize h n hn n hn
      simp at h
      exact h

    --Then, the assumption simpliifies to f n ∣ f m ↔ n∣m.
    have cla1': ∀ n ≥ 1, ∀ m ≥1 , (f n ∣ f m) ↔ (n ∣ m) := by 
      intro n nge m mge
      have : f n ∣ f m ↔ (f n) ∣ (f m - n):= by
        specialize cla1 n nge
        constructor
        intro fndfm
        exact Int.dvd_sub fndfm cla1
        intro fndn
        exact (Int.dvd_iff_dvd_of_dvd_sub fndn).mpr cla1
      rw [this]
      apply h;
      exact nge
      exact mge
    
    have cla2: ∀ n ≥ 1, f n ≤ n := by 
      intro n hn
      apply Int.le_of_dvd
      linarith
      apply cla1
      linarith

    have cla3: f 1 = 1 := by 
      specialize hf 1 (by norm_num)
      specialize cla2 1 (by norm_num)
      exact Eq.symm (Int.le_antisymm hf cla2)
      
    --Now we prove f n = n by induction. 
    have lem: ∀ x:ℕ, ∀n:ℤ, (1≤ n ∧ n ≤ x+1) → f n = n := by 
      intro x
      induction' x with x hx

      simp
      intro n nge1 nle1
      have ne1: n = 1:= by omega
      rw [ne1]; 

      exact cla3

      -- If f n < n, we get f n = f f(n) and we can use our lemma again to get f < f n.
      intro n ⟨nge1,nlexp1⟩
      by_cases t: n ≤ x+1
      apply hx
      tauto
      have nexp2: n = x+2 := by omega
      
      specialize cla2 n nge1
      by_contra fnnn 
      have : f n < n := by omega
      have : f n ≤ x+1 := by omega
      have : 1 ≤ f n := by apply hf (n); exact nge1
      have t: f (f n) = f n := by 
        apply hx
        tauto
      have : n ∣ (f n) := by 
        rw [←cla1']
        exact dvd_of_eq (id (Eq.symm t))
        linarith
        linarith
      have : n ≤ f n := by exact Int.le_of_dvd (hf n nge1) this
      linarith
       


    intro n hn
    specialize lem n.toNat n
    simp [hn] at lem
    have : n ≤ n ⊔ 0 + 1 := by 
      have : 0 ≤ n:= by linarith
      have : n ⊔ 0 = n := by exact Int.max_eq_left this
      rw [this];
      linarith
    apply lem at this
    exact this

    --From right to left. Simple calculation.
    intro h
    intro n npos m mpos
    simp_all

    