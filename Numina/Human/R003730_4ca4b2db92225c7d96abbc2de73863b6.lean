import Mathlib

-- simple solution
/-
Mitkin D:

Find all quadruples of real numbers, in each of which any number is equal to the product of any two other numbers.
 -/
theorem algebra_210643 (x : Fin 4 → ℝ) :
    ((f : Fin 3 ↪ Fin 4) → x (f 0) = x (f 1) * x (f 2)) ↔
    x ∈ ({fun _ ↦ 0, fun _ ↦ 1} : Finset (Fin 4 → ℝ)) := by
  constructor
  . intro h
    let a := x 0
    let b := x 1
    let c := x 2
    let d := x 3
    have a_eq_b_c : a = c * d :=
      h ⟨![0, 2, 3], by decide⟩
    have : b = c * d :=
      h ⟨![1, 2, 3], by decide⟩
    have a_eq_b : a = b := by linarith
    have : b = a * d :=
      h ⟨![1, 0, 3], by decide⟩
    have : c = a * d :=
      h ⟨![2, 0, 3], by decide⟩
    have b_eq_c : b = c := by linarith
    have : c = a * b :=
      h ⟨![2, 0, 1], by decide⟩
    have : d = a * b :=
      h ⟨![3, 0, 1], by decide⟩
    have c_eq_d : c = d := by linarith
    rw [←c_eq_d, ←b_eq_c, ←a_eq_b] at a_eq_b_c
    have : a * (a - 1) = 0 := by linarith
    simp at this
    simp
    rcases this with a_eq_0 | _
    . left
      ext i
      fin_cases i <;>
      . simp
        linarith
    . --have a_eq_1 : a = 1 := by linarith
      right
      ext i
      fin_cases i <;>
      . simp
        linarith
  . intro x_in
    have : ∃ x_ℤ : Fin 4 → ℤ, (∀ i, x i = x_ℤ i) ∧ x_ℤ ∈ ({fun x ↦ 0, fun x ↦ 1} : Finset (Fin 4 → ℤ)) := by
      simp at x_in ⊢
      rcases x_in with x_eq | x_eq
      . use fun x ↦ 0
        simp [x_eq]
      . use fun x ↦ 1
        simp [x_eq]
    rcases this with ⟨x_ℤ, x_eq_x_ℤ, x_ℤ_in⟩
    intro f
    repeat rw [x_eq_x_ℤ]
    norm_cast
    clear x_eq_x_ℤ
    --revert f x_ℤ_in x_ℤ
    rcases f with ⟨f', f'_inj⟩
    simp
    revert f' f'_inj x_ℤ_in x_ℤ
    decide


-- unnessarily complicated solution following the reference solution
/-
Mitkin D:

Find all quadruples of real numbers, in each of which any number is equal to the product of any two other numbers.
 -/
theorem algebra_210643' (x : Fin 4 → ℝ) :
    ((f : Fin 3 ↪ Fin 4) → x (f 0) = x (f 1) * x (f 2)) ↔
    (∃ σ : Equiv.Perm (Fin 4), x ∘ σ ∈ ({fun _ ↦ 0, fun _ ↦ 1} : Finset (Fin 4 → ℝ))) := by
  set AnyEqOtherTwoProduct := fun x : Fin 4 → ℝ ↦ (f : Fin 3 ↪ Fin 4) → x (f 0) = x (f 1) * x (f 2)
  show AnyEqOtherTwoProduct x ↔ ∃ σ : Equiv.Perm (Fin 4), x ∘ σ ∈ {fun x ↦ 0, fun x ↦ 1}
  have aeotp_under_perm (σ : Equiv.Perm (Fin 4)) : AnyEqOtherTwoProduct x ↔ AnyEqOtherTwoProduct (x ∘ σ) := by
    unfold AnyEqOtherTwoProduct
    constructor
    . intro h f
      let σ_f := f.trans σ.toEmbedding
      exact h σ_f
    . intro h f
      let σ_inv_f := f.trans σ⁻¹.toEmbedding
      have := h σ_inv_f
      simp [σ_inv_f] at this
      exact this
  constructor
  . -- $0,0,0,0,1,1,1,1,-1,,-1,1,1,-1,,-1,,-1,1$ (с точностью до перестановки чисел четверки).
    intro h
    -- Рассмотрим модули искомых чисел и упорядочим их по неубыванию: $a \leq b \leq c \leq d$.
    let σ := Tuple.sort x
    use σ
    set x' := x ∘ σ
    let a := x' 0
    let b := x' 1
    let c := x' 2
    let d := x' 3
    have monotone : Monotone x' := by
      exact Tuple.monotone_sort x
    have : a ≤ b := monotone (by simp)
    have : b ≤ c := monotone (by simp)
    have : c ≤ d := monotone (by simp)
    -- Заметим, что $a \geq b c$, так как либо $a=b c$, либо $a=b d \geq b c$, либо $a=c d \geq b c$. Аналогично, $d \leq b c$. Следовательно, $b c \leq a \leq b \leq c \leq d \leq b c$, т.е. $a=b=c=d=b c=x$. Так как $x=x^{2}$, то $x=0$ или $x=1$. Остается проверить, что если в четверке есть отрицательные числа, то их количество равно двум или трем.
    rw [aeotp_under_perm σ] at h
    change AnyEqOtherTwoProduct x' at h
    have a_eq_b_c : a = b * c :=
      h ⟨![0, 1, 2], by decide⟩
    have : d = b * c :=
      h ⟨![3, 1, 2], by decide⟩
    have a_eq_b : a = b := by linarith
    have b_eq_c : b = c := by linarith
    have : c = d := by linarith
    rw [←b_eq_c, ←a_eq_b] at a_eq_b_c
    have : a * (a - 1) = 0 := by linarith
    simp at this
    simp
    rcases this with a_eq_0 | _
    . left
      ext i
      fin_cases i <;>
      . simp
        linarith
    . --have a_eq_1 : a = 1 := by linarith
      right
      ext i
      fin_cases i <;>
      . simp
        linarith
    /-
    ## Oтвет

    $0,0,0,0,1,1,1,1,-1,-1,1,1,-1,-1,-1,1$ (с точностью до перестановки чисел четверки).
    -/
    -- The last 2 solutions in the reference solution comment above are incorrect.
  . rintro ⟨σ, x_σ_in⟩
    rw [aeotp_under_perm σ]
    generalize x ∘ σ = x' at x_σ_in ⊢
    unfold AnyEqOtherTwoProduct
    have : ∃ x'_ℤ : Fin 4 → ℤ, (∀ i, x' i = x'_ℤ i) ∧ x'_ℤ ∈ ({fun x ↦ 0, fun x ↦ 1} : Finset (Fin 4 → ℤ)) := by
      simp at x_σ_in ⊢
      rcases x_σ_in with x'_eq | x'_eq
      . use fun x ↦ 0
        simp [x'_eq]
      . use fun x ↦ 1
        simp [x'_eq]
    rcases this with ⟨x'_ℤ, x'_eq_x'_ℤ, x'_ℤ_in⟩
    intro f
    repeat rw [x'_eq_x'_ℤ]
    norm_cast
    clear x'_eq_x'_ℤ
    --revert f x'_ℤ_in x'_ℤ
    rcases f with ⟨f', f'_inj⟩
    simp
    revert f' f'_inj x'_ℤ_in x'_ℤ
    decide
