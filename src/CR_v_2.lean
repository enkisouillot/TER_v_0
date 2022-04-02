import analysis.complex.basic -- pour travailler sur ℂ
import analysis.calculus.deriv -- pour utiliser la dérivation déjà créée de façon générale

noncomputable theory -- pour ne pas avoir de problèmes sur les définitions

/-
Tout d'abord, voici les applications linéaires (et continues) naturelles entre ℂ et ℝ²
-/

def C_to_R2 : ℂ →L[ℝ] ℝ × ℝ := complex.equiv_real_prodₗ -- l'application de ℂ ≃ ℝ²
def R2_to_C : ℝ × ℝ →L[ℝ] ℂ := complex.equiv_real_prodₗ.symm -- sa réciproque

/-
Puis, la propriété qui transforme une fonction complexe en sa réalification dans ℝ²
-/

def realify (f : ℂ → ℂ) : ℝ × ℝ → ℝ × ℝ := C_to_R2 ∘ f ∘ R2_to_C 

/-
  On souhaite ensuite montrer que la multiplication par un complexe est une application ℂ-linéaire et continue de ℂ dans ℂ
  Voici la méthode :
-/

def multiplication (w : ℂ) : ℂ →L[ℂ] ℂ :=
begin
  refine ⟨_,_⟩, -- on demande à LEAN de générer les objectifs de la définition
  {
    refine ⟨_,_,_⟩, -- encore une fois
    exact λ z, w * z, -- LEAN veut une application de ℂ dans ℂ, on lui donne la multiplication par w ∈ ℂ
    exact mul_add w, -- on trouve ensuite la propriété de linéarité (on utilise notamment library_search)
    intros, simp, ring, -- on termine avec des tactiques simples
  },
  simp, -- on demande à LEAN de simplifier pour y voir clair
  exact continuous_mul_left w, -- encore un library_search pour trouver la propriété dans mathlib
end 

/-
On peut ensuite essayer de réduire la taille de cette preuve : on remplace les _ des refine
par les propriétés, directement dans les ⟨⟩
-/

def multiply (w : ℂ) :  ℂ →L[ℂ] ℂ :=
⟨⟨λ z, w * z, mul_add w, by { intros, simp, ring }⟩, continuous_mul_left w⟩

/- 
  On montre ensuite que cette multiplication est aussi une application ℝ-linéaire continue de ℂ dans ℂ
-/

def real_multiply (f' : ℂ) : ℂ →L[ℝ] ℂ :=
continuous_linear_map.restrict_scalars ℝ (multiply f')

/-
  Nous arrivons enfin au point crucial : montrer les équations de Cauchy-Riemann
  Le théorème que nous voulons montrer dit qu'une fonction complexe qui est ℂ-dérivable
  de dérivée f' est aussi ℝ²-dérivable de dérivée la multiplication par f'
  Voici l'énoncé LEAN :
-/

lemma cauchy_riemann_step_1 {f : ℂ → ℂ} {z : ℂ} (f' : ℂ) (hf : has_deriv_at f f' z) : -- les variables et les hypothèses
  has_fderiv_at (realify f) (C_to_R2 ∘L real_multiply f' ∘L R2_to_C) (C_to_R2 z) := -- l'énoncé
begin
  refine C_to_R2.has_fderiv_at.comp _ (has_fderiv_at.comp _ _ R2_to_C.has_fderiv_at), -- pourquoi 2 _ dans la parenthèse ? Quel rôle du . dans les propriétés ?
  have zz : function.left_inverse R2_to_C C_to_R2 := complex.equiv_real_prod.left_inv, rw zz z,
  convert has_fderiv_at.restrict_scalars ℝ hf.has_fderiv_at,
  simp [real_multiply, multiply, continuous_linear_map.restrict_scalars],
  apply linear_map.ext, intro z, simp, apply mul_comm
end

example {f : ℂ → ℂ} {z : ℂ} (f' : ℂ) (hf : has_deriv_at f f' z) :
  has_fderiv_at (realify f) (C_to_R2 ∘L real_multiply f' ∘L R2_to_C) (C_to_R2 z) :=
begin
  apply has_fderiv_at.comp,
  { apply C_to_R2.has_fderiv_at},
  {apply has_fderiv_at.comp,
  { sorry},
  {apply R2_to_C.has_fderiv_at, }, },
  -- refine C_to_R2.has_fderiv_at.comp _ (has_fderiv_at.comp _ _ R2_to_C.has_fderiv_at),
end