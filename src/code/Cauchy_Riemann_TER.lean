import analysis.complex.basic -- pour travailler sur ℂ
import analysis.calculus.deriv -- pour utiliser la dérivation déjà créée de façon générale
import data.matrix.notation

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

def realifyₗ (f : ℂ →L[ℝ] ℂ) : ℝ × ℝ →L[ℝ] ℝ × ℝ := C_to_R2 ∘L f ∘L R2_to_C

example {f : ℂ → ℂ} {z : ℂ} (f' : ℂ) (hf : has_deriv_at f f' z) :
  has_fderiv_at (realify f) (realifyₗ (real_multiply f')) (C_to_R2 z) :=
begin
  -- On donne la preuve que R2_to_C est l'inverse à gauche de C_to_R2
  have zz : function.left_inverse R2_to_C C_to_R2 := complex.equiv_real_prod.left_inv,
  -- on applique la règle de dérivation en chaîne
  apply has_fderiv_at.comp,
  -- la preuve que C_to_R2 soit différentiable de différentielle elle-même est :
  { apply C_to_R2.has_fderiv_at},
  -- on applique encore une fois la règle de la chaîne
  {apply has_fderiv_at.comp,
  -- on demande à LEAN de comparer l'hypohtèse hf restreinte à ℝ avec le goal
  -- LEAN donne alors à prouver les différences
  { convert has_fderiv_at.restrict_scalars ℝ hf.has_fderiv_at,
    -- on simplifie le goal : on développe real_multiply, puis multiply
    { simp [real_multiply, multiply, continuous_linear_map.restrict_scalars],
      -- deux applications sont égales si elles sont égales en tout point
      apply linear_map.ext, intro x, simp, apply mul_comm
    }, -- il reste maintenant à appliquer l'hypothèse zz que nous avions montrée
    { apply zz},},
  -- et voici la preuve que R2_to_C est différentiable de différentielle elle-même
  {apply R2_to_C.has_fderiv_at, }, },
end

/-
Il reste alors à rendre cette preuve plus courte avec une écriture condensée
-/

lemma cauchy_riemann_step_1 {f : ℂ → ℂ} {z : ℂ} (f' : ℂ) (hf : has_deriv_at f f' z) : 
  has_fderiv_at (realify f) (realifyₗ (real_multiply f')) (C_to_R2 z) := 
begin
  refine C_to_R2.has_fderiv_at.comp _ (has_fderiv_at.comp _ _ R2_to_C.has_fderiv_at),
  have zz : function.left_inverse R2_to_C C_to_R2 := complex.equiv_real_prod.left_inv, 
  rw zz z,
  convert has_fderiv_at.restrict_scalars ℝ hf.has_fderiv_at,
  simp [real_multiply, multiply, continuous_linear_map.restrict_scalars],
  apply linear_map.ext, intro z, simp, apply mul_comm,
end

-- je teste l'ancienne version de la multiplication, avec la nouvelle définition de realify

def mul_exe (z : ℂ) : (ℝ × ℝ →L[ℝ] ℝ × ℝ) := by {
  refine ⟨_,_⟩, -- on recommence les refine, comme avant
  { refine ⟨_,_,_⟩,
    -- on veut la multiplication par z, mais de ℝ² dans ℝ²
    { exact realify (λ w, w * z) }, 
    -- LEAN prouve l'additivité avec la tactique ring
    { intros, simp [realify], ring}, 
    -- on continue avec l'homogénéité, encore une fois avec ring,
    { intros, simp[realify, C_to_R2], split ; ring }, 
  },
  -- on simplifie et on applique la règle de continuité sur la composition
  simp [realify], apply continuous.comp,
  -- C_to_R2 est continue
  { exact C_to_R2.continuous },
  -- encore la continuité de la composition
  apply continuous.comp,
  -- la multiplication à droite est continue
  { exact continuous_mul_right z },
  -- R2_to_C est continue
  { exact R2_to_C.continuous },
}

/-
La deuxième étape de notre développement est de considérer les matrices et notamment la matrice
de notre application de multiplication
On souhaite en effet exprimer des relations entre les dérivées partielles
que l'on peut voir comme étant les coefficients de la matrice de f' dans la base canonique
Si l'on prouve que la matrice est bel et bien de la forme d'une matrice de multiplication
on aura directement les relations souhaitée
-/

-- Voici la définition d'une matrice de multiplication

def mulmatrix (a b : ℝ) : matrix (fin 2) (fin 2) ℝ :=
![![a,  -b],
  ![b,  a]]

/-
Et voici l'énoncé disant que l'application
-/

lemma cauchy_riemann_step_2 (f' : ℂ) : 
  (fin_two_arrow_equiv ℝ) ∘ matrix.to_lin' (mulmatrix (f'.re) (f'.im)) ∘ (fin_two_arrow_equiv ℝ).symm 
    = realifyₗ (real_multiply f') :=
begin
  funext, -- deux fonctions sont les mêmes si elles sont les mêmes sur tout élément de l'ensemble
  simp [realifyₗ, C_to_R2, R2_to_C],
  simp [mulmatrix],
  simp [real_multiply],
  simp [multiply],
  split ; ring,
end

-- Une fonction dans un sens
def lin_matrix : (fin 2 → ℝ) →ₗ[ℝ] ℝ × ℝ := linear_equiv.fin_two_arrow ℝ ℝ
-- celle dans l'autre sens, rien d'autre que la réciproque
def lin_matrix_symm : ℝ × ℝ →ₗ[ℝ] (fin 2 → ℝ) := (linear_equiv.fin_two_arrow ℝ ℝ).symm
-- la composition des deux en une seule fonction
def linify (f : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) : (fin 2 → ℝ) →ₗ[ℝ] (fin 2 → ℝ) := 
lin_matrix_symm ∘ₗ f ∘ₗ lin_matrix

-- On définit enfin la matrice de la différentielle d'une application f

def matrix_diff (f' : ℂ) : matrix (fin 2) (fin 2) ℝ := 
  linear_map.to_matrix' (linify (continuous_linear_map.simps.coe (realifyₗ (real_multiply f'))))

-- On en arrive aux définitions des dérivées partielles des parties réelles et imaginaires
-- comme des vecteurs, venant de la matrice de la différentielle

def partial_deriv_re (f' : ℂ) : fin 2 → ℝ := matrix_diff f' 0
def partial_deriv_im (f' : ℂ) : fin 2 → ℝ := matrix_diff f' 1

/-
Et enfin, la preuve des égalités de Cauchy-Riemann, bien connues
-/

lemma cauchy_riemann_step_3 (f' : ℂ) :
(partial_deriv_re f' 0) = (partial_deriv_im f' 1) ∧ (partial_deriv_re f' 1) = -(partial_deriv_im f' 0) :=
begin
simp [partial_deriv_re, partial_deriv_im, matrix_diff, linify, lin_matrix_symm,
  lin_matrix, realifyₗ, real_multiply, multiply, C_to_R2, R2_to_C,
  continuous_linear_map.comp, linear_map.comp, continuous_linear_map.simps.coe],
end