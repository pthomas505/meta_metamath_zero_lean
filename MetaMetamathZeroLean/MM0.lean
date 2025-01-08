import MathlibExtra.FunctionUpdateITE

import Mathlib.Util.CompileInductive


set_option autoImplicit false


namespace MM0


/--
  The type of variable names.
-/
inductive VarName : Type
  | mk : String → VarName
  deriving Inhabited, DecidableEq

/--
  The string representation of variable names.
-/
def VarName.toString : VarName → String
  | VarName.mk x => x

instance : ToString VarName :=
  { toString := fun x => x.toString }

instance : Repr VarName :=
  { reprPrec := fun x _ => x.toString.toFormat }


/--
  The type of meta variable names.
-/
inductive MetaVarName : Type
  | mk : String → MetaVarName
  deriving Inhabited, DecidableEq

/--
  The string representation of meta variable names.
-/
def MetaVarName.toString : MetaVarName → String
  | MetaVarName.mk X => X

instance : ToString MetaVarName :=
  { toString := fun X => X.toString }

instance : Repr MetaVarName :=
  { reprPrec := fun X _ => X.toString.toFormat }


/--
  The type of predicate names.
-/
inductive PredName : Type
  | mk : String → PredName
  deriving Inhabited, DecidableEq

/--
  The string representation of predicate names.
-/
def PredName.toString : PredName → String
  | PredName.mk X => X

instance : ToString PredName :=
  { toString := fun X => X.toString }

instance : Repr PredName :=
  { reprPrec := fun X _ => X.toString.toFormat }


/--
  The type of definition names.
-/
inductive DefName : Type
  | mk : String → DefName
  deriving Inhabited, DecidableEq

/--
  The string representation of definition names.
-/
def DefName.toString : DefName → String
  | DefName.mk X => X

instance : ToString DefName :=
  { toString := fun X => X.toString }

instance : Repr DefName :=
  { reprPrec := fun X _ => X.toString.toFormat }


/--
  The type of formulas.
-/
inductive Formula : Type
  | meta_var_ : MetaVarName → Formula
  | pred_ : PredName → List VarName → Formula
  | eq_ : VarName → VarName → Formula
  | true_ : Formula
  | not_ : Formula → Formula
  | imp_ : Formula → Formula → Formula
  | forall_ : VarName → Formula → Formula
  | def_ : DefName → List VarName → Formula
  deriving Inhabited, DecidableEq

compile_inductive% Formula

open Formula


/--
  (v, X) ∈ Γ if and only if v is not free in X.

  NotFree Γ v F := True if and only if v is not free in F in the context Γ.
-/
def NotFree
  (Γ : List (VarName × MetaVarName))
  (v : VarName) :
  Formula → Prop
  | meta_var_ X => (v, X) ∈ Γ
  | pred_ _ xs => v ∉ xs
  | eq_ x y => ¬ x = v ∧ ¬ y = v
  | true_ => True
  | not_ phi => NotFree Γ v phi
  | imp_ phi psi => NotFree Γ v phi ∧ NotFree Γ v psi
  | forall_ x phi => x = v ∨ NotFree Γ v phi
  | def_ _ xs => v ∉ xs


instance
  (Γ : List (VarName × MetaVarName))
  (v : VarName)
  (F : Formula) :
  Decidable (NotFree Γ v F) :=
  by
  induction F
  all_goals
    unfold NotFree
    infer_instance


/--
  Formula.metaVarSet F := The set of all of the meta variables that have an occurrence in the formula F.
-/
def Formula.metaVarSet :
  Formula → Finset MetaVarName
  | meta_var_ X => {X}
  | pred_ _ _ => ∅
  | eq_ _ _ => ∅
  | true_ => ∅
  | not_ phi => phi.metaVarSet
  | imp_ phi psi => phi.metaVarSet ∪ psi.metaVarSet
  | forall_ _ phi => phi.metaVarSet
  | def_ _ _ => ∅


/--
  NoMetaVarAndAllFreeInList vs F := True if and only if F contains no meta variables and all of the variables that occur free in F are in vs.
-/
def NoMetaVarAndAllFreeInList
  (vs : List VarName) :
  Formula → Prop
  | meta_var_ _ => False
  | pred_ _ xs => xs ⊆ vs
  | eq_ x y => x ∈ vs ∧ y ∈ vs
  | true_ => True
  | not_ phi =>
      NoMetaVarAndAllFreeInList vs phi
  | imp_ phi psi =>
      NoMetaVarAndAllFreeInList vs phi ∧
      NoMetaVarAndAllFreeInList vs psi
  | forall_ x phi =>
      NoMetaVarAndAllFreeInList (x :: vs) phi
  | def_ _ xs => xs ⊆ vs


/--
  A substitution mapping.
  A bijective function mapping variable names to variable names.
-/
def Instantiation : Type :=
  { σ : VarName → VarName // ∃ σ' : VarName → VarName, σ ∘ σ' = id ∧ σ' ∘ σ = id }


def Instantiation.comp
  (σ σ' : Instantiation) :
  Instantiation :=
  {
    val := σ.val ∘ σ'.val
    property :=
    by
      obtain ⟨σ_inv_val, σ_inv_prop⟩ := σ.2
      obtain ⟨σ'_inv_val, σ'_inv_prop⟩ := σ'.2
      cases σ_inv_prop
      case intro σ_inv_prop_left σ_inv_prop_right =>
        cases σ'_inv_prop
        case intro σ'_inv_prop_left σ'_inv_prop_right =>
        apply Exists.intro (σ'_inv_val ∘ σ_inv_val)
        constructor
        · change σ.val ∘ (σ'.val ∘ σ'_inv_val) ∘ σ_inv_val = id
          simp only [σ'_inv_prop_left]
          simp
          exact σ_inv_prop_left
        · change σ'_inv_val ∘ (σ_inv_val ∘ σ.val) ∘ σ'.val = id
          simp only [σ_inv_prop_right]
          simp
          exact σ'_inv_prop_right
  }


/--
  A meta variable substitution mapping.
  A function mapping meta variable names to formulas.
-/
def MetaInstantiation : Type := MetaVarName → Formula


def sub
  (σ : Instantiation)
  (τ : MetaInstantiation) :
  Formula → Formula
  | meta_var_ X => τ X
  | pred_ X xs => pred_ X (xs.map σ.1)
  | eq_ x y => eq_ (σ.1 x) (σ.1 y)
  | true_ => true_
  | not_ phi => not_ (sub σ τ phi)
  | imp_ phi psi => imp_ (sub σ τ phi) (sub σ τ psi)
  | forall_ x phi => forall_ (σ.1 x) (sub σ τ phi)
  | def_ X xs => def_ X (xs.map σ.1)


structure Definition : Type :=
  name : DefName
  args : List VarName
  F : Formula
  nodup : args.Nodup
  nf : NoMetaVarAndAllFreeInList args F
  deriving DecidableEq


abbrev Env : Type := List Definition

def Env.Nodup : Env → Prop :=
  List.Pairwise fun d1 d2 : Definition =>
    d1.name = d2.name → d1.args.length = d2.args.length → False


/--
  IsMetaVarOrAllDefInEnv E F := True if and only if F is a meta variable or every definition in F is defined in E.
-/
def IsMetaVarOrAllDefInEnv
  (E : Env) :
  Formula → Prop
  | meta_var_ _ => True
  | pred_ _ _ => True
  | eq_ _ _ => True
  | true_ => True
  | not_ phi => IsMetaVarOrAllDefInEnv E phi
  | imp_ phi psi =>
    IsMetaVarOrAllDefInEnv E phi ∧
    IsMetaVarOrAllDefInEnv E psi
  | forall_ _ phi => IsMetaVarOrAllDefInEnv E phi
  | def_ X xs =>
      ∃ d : Definition,
        d ∈ E ∧
        X = d.name ∧
        xs.length = d.args.length


def Env.WellFormed : Env → Prop
  | List.nil => True
  | d :: E =>
    (∀ d' : Definition, d' ∈ E →
      d.name = d'.name → d.args.length = d'.args.length → False) ∧
        IsMetaVarOrAllDefInEnv E d.F ∧ Env.WellFormed E


inductive IsConv (E : Env) : Formula → Formula → Prop
  | conv_refl
    (phi : Formula) :
    IsConv E phi phi

  | conv_symm
    (phi phi' : Formula) :
    IsConv E phi phi' →
    IsConv E phi' phi

  | conv_trans
    (phi phi' phi'' : Formula) :
    IsConv E phi phi' →
    IsConv E phi' phi'' →
    IsConv E phi phi''

  | conv_not
    (phi phi' : Formula) :
    IsConv E phi phi' →
    IsConv E (not_ phi) (not_ phi')

  | conv_imp
    (phi phi' psi psi' : Formula) :
    IsConv E phi phi' →
    IsConv E psi psi' →
    IsConv E (imp_ phi psi) (imp_ phi' psi')

  | conv_forall
    (x : VarName)
    (phi phi' : Formula) :
    IsConv E phi phi' →
    IsConv E (forall_ x phi) (forall_ x phi')

  | conv_unfold
    (d : Definition)
    (σ : Instantiation) :
    d ∈ E →
    IsConv E (def_ d.name (d.args.map σ.1)) (sub σ meta_var_ d.F)


def Formula.false_ : Formula := not_ true_

def Formula.and_
  (phi psi : Formula) :
  Formula :=
  not_ (phi.imp_ psi.not_)

def Formula.exists_
  (x : VarName)
  (phi : Formula) :
  Formula :=
  not_ (forall_ x (not_ phi))


def Formula.And_
  (l : List Formula) :
  Formula :=
  List.foldr Formula.and_ true_ l

def eqSubPred
  (name : PredName)
  (n : ℕ)
  (xs ys : Fin n → VarName) :
  Formula :=
  (And_ (List.ofFn fun i : Fin n => eq_ (xs i) (ys i))).imp_
    ((pred_ name (List.ofFn xs)).imp_ (pred_ name (List.ofFn ys)))


/-
  (v, X) ∈ Γ if and only if v is not free in X.

  Δ is a list of hypotheses.
-/
inductive IsProof
  (E : Env) :
  List (VarName × MetaVarName) → List Formula → Formula → Prop

  | hyp
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi : Formula) :
    IsMetaVarOrAllDefInEnv E phi →
    phi ∈ Δ →
    IsProof E Γ Δ phi

  | mp
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi psi : Formula) :
    IsProof E Γ Δ phi →
    IsProof E Γ Δ (phi.imp_ psi) →
    IsProof E Γ Δ psi

  | prop_1
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi psi : Formula) :
    IsMetaVarOrAllDefInEnv E phi →
    IsMetaVarOrAllDefInEnv E psi →
    IsProof E Γ Δ (phi.imp_ (psi.imp_ phi))

  | prop_2
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi psi chi : Formula) :
    IsMetaVarOrAllDefInEnv E phi →
    IsMetaVarOrAllDefInEnv E psi →
    IsMetaVarOrAllDefInEnv E chi →
    IsProof E Γ Δ ((phi.imp_ (psi.imp_ chi)).imp_ ((phi.imp_ psi).imp_ (phi.imp_ chi)))

  | prop_3
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi psi : Formula) :
    IsMetaVarOrAllDefInEnv E phi →
    IsMetaVarOrAllDefInEnv E psi →
    IsProof E Γ Δ (((not_ phi).imp_ (not_ psi)).imp_ (psi.imp_ phi))

  | gen
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi : Formula)
    (x : VarName) :
    IsProof E Γ Δ phi →
    IsProof E Γ Δ (forall_ x phi)

  | pred_1
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi psi : Formula)
    (x : VarName) :
    IsMetaVarOrAllDefInEnv E phi →
    IsMetaVarOrAllDefInEnv E psi →
    IsProof E Γ Δ ((forall_ x (phi.imp_ psi)).imp_ ((forall_ x phi).imp_ (forall_ x psi)))

  | pred_2
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi : Formula)
    (x : VarName) :
    IsMetaVarOrAllDefInEnv E phi →
    NotFree Γ x phi →
    IsProof E Γ Δ (phi.imp_ (forall_ x phi))

  | eq_1
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (x y : VarName) :
    ¬ y = x →
    IsProof E Γ Δ (exists_ x (eq_ x y))

  | eq_2
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (x y z : VarName) :
    IsProof E Γ Δ ((eq_ x y).imp_ ((eq_ x z).imp_ (eq_ y z)))

  | eq_3
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (n : ℕ)
    (name : PredName)
    (xs ys : Fin n → VarName) :
    IsProof E Γ Δ (eqSubPred name n xs ys)

  | thm
    (Γ Γ' : List (VarName × MetaVarName))
    (Δ Δ' : List Formula)
    (phi : Formula)
    (σ : Instantiation)
    (τ : MetaInstantiation) :
    (∀ X : MetaVarName, X ∈ phi.metaVarSet →
    IsMetaVarOrAllDefInEnv E (τ X)) →
    (∀ (x : VarName) (X : MetaVarName), (x, X) ∈ Γ → NotFree Γ' (σ.1 x) (τ X)) →
    (∀ psi : Formula, psi ∈ Δ → IsProof E Γ' Δ' (sub σ τ psi)) →
    IsProof E Γ Δ phi →
    IsProof E Γ' Δ' (sub σ τ phi)

  | conv
    (Γ : List (VarName × MetaVarName))
    (Δ : List Formula)
    (phi phi' : Formula) :
    IsMetaVarOrAllDefInEnv E phi' →
    IsProof E Γ Δ phi →
    IsConv E phi phi' →
    IsProof E Γ Δ phi'


def Interpretation (D : Type) : Type :=
  PredName → List D → Prop

def Valuation (D : Type) : Type :=
  VarName → D

def MetaValuation (D : Type) : Type :=
  MetaVarName → Valuation D → Prop


def Holds
  (D : Type)
  (I : Interpretation D)
  (V : Valuation D)
  (M : MetaValuation D) : Env → Formula → Prop
  | _, meta_var_ X => M X V
  | _, pred_ X xs => I X (xs.map V)
  | _, eq_ x y => V x = V y
  | _, true_ => True
  | E, not_ phi => ¬ Holds D I V M E phi
  | E, imp_ phi psi =>
    have : sizeOf psi < sizeOf (imp_ phi psi) := by simp
    Holds D I V M E phi → Holds D I V M E psi
  | E, forall_ x phi =>
    have : sizeOf phi < sizeOf (forall_ x phi) := by simp
    ∀ d : D, Holds D I (Function.updateITE V x d) M E phi
  | ([] : Env), def_ _ _ => False
  | d :: E, def_ name args =>
    if name = d.name ∧ args.length = d.args.length
    then Holds D I (Function.updateListITE V d.args (List.map V args)) M E d.F
    else Holds D I V M E (def_ name args)
termination_by E phi => (E.length, phi)


/-
  Changing v does not cause the value of F to change.
-/
def IsNotFree
  (D : Type)
  (I : Interpretation D)
  (M : MetaValuation D)
  (E : Env)
  (F : Formula)
  (v : VarName) :
  Prop :=
  ∀ (V : Valuation D) (d : D),
    Holds D I V M E F ↔
      Holds D I (Function.updateITE V v d) M E F


example
  (F : Formula)
  (vs vs' : List VarName)
  (h1 : NoMetaVarAndAllFreeInList vs F)
  (h2 : vs ⊆ vs') :
  NoMetaVarAndAllFreeInList vs' F :=
  by
  induction F generalizing vs vs'
  case meta_var_ X =>
    unfold NoMetaVarAndAllFreeInList at h1

    contradiction
  case pred_ X xs =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NoMetaVarAndAllFreeInList
    exact Set.Subset.trans h1 h2
  case eq_ x y =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NoMetaVarAndAllFreeInList
    cases h1
    case intro h1_left h1_right =>
    constructor
    · exact h2 h1_left
    · exact h2 h1_right
  case true_ =>
    unfold NoMetaVarAndAllFreeInList
    simp
  case not_ phi phi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NoMetaVarAndAllFreeInList
    exact phi_ih vs vs' h1 h2
  case imp_ phi psi phi_ih psi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NoMetaVarAndAllFreeInList
    cases h1
    case intro h1_left h1_right =>
    constructor
    · exact phi_ih vs vs' h1_left h2
    · exact psi_ih vs vs' h1_right h2
  case forall_ x phi phi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NoMetaVarAndAllFreeInList
    apply phi_ih (x :: vs) (x :: vs') h1
    exact List.cons_subset_cons x h2
  case def_ X xs =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NoMetaVarAndAllFreeInList
    exact Set.Subset.trans h1 h2


theorem all_free_in_list_and_not_in_list_imp_not_free
  (F : Formula)
  (vs : List VarName)
  (v : VarName)
  (Γ : List (VarName × MetaVarName))
  (h1 : NoMetaVarAndAllFreeInList vs F)
  (h2 : v ∉ vs) :
  NotFree Γ v F :=
  by
  induction F generalizing vs
  case meta_var_ X =>
    unfold NoMetaVarAndAllFreeInList at h1

    contradiction
  case pred_ X xs =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NotFree
    tauto
  case eq_ x y =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NotFree
    cases h1
    case intro h1_left h1_right =>
      constructor
      · intro contra
        apply h2
        subst contra
        exact h1_left
      · intro contra
        apply h2
        subst contra
        exact h1_right
  case true_ =>
    unfold NotFree
    simp
  case not_ phi phi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NotFree
    exact phi_ih vs h1 h2
  case imp_ phi psi phi_ih psi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NotFree
    cases h1
    case intro h1_left h1_right =>
      constructor
      · exact phi_ih vs h1_left h2
      · exact psi_ih vs h1_right h2
  case forall_ x phi phi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NotFree
    by_cases c1 : x = v
    · left
      exact c1
    · right
      apply phi_ih (x :: vs) h1
      simp
      push_neg
      constructor
      · tauto
      · exact h2
  case def_ X xs =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold NotFree
    tauto


theorem no_meta_var_imp_meta_var_set_is_empty
  (F : Formula)
  (vs : List VarName)
  (h1 : NoMetaVarAndAllFreeInList vs F) :
  F.metaVarSet = ∅ :=
  by
  induction F generalizing vs
  case meta_var_ X =>
    unfold NoMetaVarAndAllFreeInList at h1

    contradiction
  case pred_ X xs =>
    rfl
  case eq_ x y =>
    rfl
  case true_ =>
    rfl
  case not_ phi phi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold Formula.metaVarSet
    exact phi_ih vs h1
  case imp_ phi psi phi_ih psi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold Formula.metaVarSet
    cases h1
    case intro h1_left h1_right =>
      simp only [phi_ih vs h1_left]
      simp only [psi_ih vs h1_right]
      simp
  case forall_ x phi phi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold Formula.metaVarSet
    exact phi_ih (x :: vs) h1
  case def_ X xs =>
    rfl


theorem Instantiation.has_left_right_inverse
  (σ : Instantiation) :
  ∃ σ_inv : Instantiation, σ.1 ∘ σ_inv.1 = id ∧ σ_inv.1 ∘ σ.1 = id :=
  by
  apply Exists.elim σ.2
  intro σ' a1
  cases a1
  case intro a1_left a1_right =>
    let σ_inv : Instantiation :=
    {
      val := σ'
      property :=
      by
        apply Exists.intro σ.1
        constructor
        · exact a1_right
        · exact a1_left
    }
    apply Exists.intro σ_inv
    constructor
    · exact a1_left
    · exact a1_right


theorem Instantiation.is_injective
  (σ : Instantiation) :
  Function.Injective σ.1 :=
  by
  obtain ⟨σ', a1⟩ := σ.2
  cases a1
  case intro a1_left a1_right =>
    have s1 : Function.LeftInverse σ' σ.1 := congr_fun a1_right
    exact Function.LeftInverse.injective s1


theorem Instantiation.is_surjective
  (σ : Instantiation) :
  Function.Surjective σ.1 :=
  by
  obtain ⟨σ', a1⟩ := σ.2
  cases a1
  case intro a1_left a1_right =>
    have s1 : Function.RightInverse σ' σ.1 := congr_fun a1_left
    exact Function.RightInverse.surjective s1


theorem Instantiation.is_bijective
  (σ : Instantiation) :
  Function.Bijective σ.1 :=
  by
  unfold Function.Bijective
  constructor
  · exact Instantiation.is_injective σ
  · exact Instantiation.is_surjective σ


theorem sub_of_sub_is_sub_of_instantiation_comp
  (F : Formula)
  (σ σ' : Instantiation) :
  sub σ Formula.meta_var_ (sub σ' Formula.meta_var_ F) =
    sub (Instantiation.comp σ σ') Formula.meta_var_ F :=
  by
  induction F
  case meta_var_ X =>
    rfl
  case pred_ X xs =>
    simp only [sub]
    unfold Instantiation.comp
    simp
  case eq_ x y =>
    rfl
  case true_ =>
    rfl
  case not_ phi phi_ih =>
    simp only [sub]
    unfold Instantiation.comp
    congr! 1
  case imp_ phi psi phi_ih psi_ih =>
    simp only [sub]
    unfold Instantiation.comp
    congr! 1
  case forall_ x phi phi_ih =>
    simp only [sub]
    unfold Instantiation.comp
    congr! 1
  case def_ X xs =>
    simp only [sub]
    unfold Instantiation.comp
    simp


theorem sub_preserves_empty_meta_var_set
  (F : Formula)
  (σ : Instantiation)
  (τ : MetaInstantiation)
  (h1 : F.metaVarSet = ∅) :
  (sub σ τ F).metaVarSet = ∅ :=
  by
  induction F
  case meta_var_ X =>
    unfold Formula.metaVarSet at h1
    simp at h1
  case pred_ X xs =>
    rfl
  case eq_ x y =>
    rfl
  case true_ =>
    rfl
  case not_ phi phi_ih =>
    unfold Formula.metaVarSet at h1

    unfold sub
    unfold Formula.metaVarSet
    exact phi_ih h1
  case imp_ phi psi phi_ih psi_ih =>
    unfold Formula.metaVarSet at h1
    simp only [Finset.union_eq_empty] at h1

    unfold sub
    unfold Formula.metaVarSet
    cases h1
    case intro h1_left h1_right =>
      simp only [Finset.union_eq_empty]
      constructor
      · exact phi_ih h1_left
      · exact psi_ih h1_right
  case forall_ x phi phi_ih =>
    unfold Formula.metaVarSet at h1

    unfold sub
    unfold Formula.metaVarSet
    exact phi_ih h1
  case def_ X xs =>
    rfl


theorem no_meta_var_imp_meta_instantiation_irrelevance_in_sub
  (F : Formula)
  (σ : Instantiation)
  (τ τ' : MetaInstantiation)
  (h1 : F.metaVarSet = ∅) :
  sub σ τ F = sub σ τ' F :=
  by
  induction F
  case meta_var_ X =>
    unfold Formula.metaVarSet at h1
    simp at h1
  case pred_ X xs =>
    rfl
  case eq_ x y =>
    rfl
  case true_ =>
    rfl
  case not_ phi phi_ih =>
    unfold Formula.metaVarSet at h1

    unfold sub
    congr! 1
    exact phi_ih h1
  case imp_ phi psi phi_ih psi_ih =>
    unfold Formula.metaVarSet at h1
    simp only [Finset.union_eq_empty] at h1

    unfold sub
    cases h1
    case intro h1_left h1_right =>
    congr! 1
    · exact phi_ih h1_left
    · exact psi_ih h1_right
  case forall_ x phi phi_ih =>
    unfold Formula.metaVarSet at h1

    unfold sub
    congr! 1
    exact phi_ih h1
  case def_ X xs =>
    rfl


theorem no_meta_var_and_all_free_in_list_map_sub
  (F : Formula)
  (vs : List VarName)
  (σ : Instantiation)
  (τ : MetaInstantiation)
  (h1 : NoMetaVarAndAllFreeInList vs F) :
  NoMetaVarAndAllFreeInList (vs.map σ.1) (sub σ τ F) :=
  by
  induction F generalizing vs
  case meta_var_ X =>
    unfold NoMetaVarAndAllFreeInList at h1

    contradiction
  case pred_ X xs =>
    unfold sub
    unfold NoMetaVarAndAllFreeInList
    exact List.map_subset σ.1 h1
  case true_ =>
    unfold sub
    unfold NoMetaVarAndAllFreeInList
    simp
  case not_ phi phi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold sub
    unfold NoMetaVarAndAllFreeInList
    exact phi_ih vs h1
  case imp_ phi psi phi_ih psi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold sub
    unfold NoMetaVarAndAllFreeInList
    cases h1
    case intro h1_left h1_right =>
      constructor
      · exact phi_ih vs h1_left
      · exact psi_ih vs h1_right
  case eq_ x y =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold sub
    unfold NoMetaVarAndAllFreeInList
    cases h1
    case intro h1_left h1_right =>
      constructor
      · exact List.mem_map_of_mem σ.val h1_left
      · exact List.mem_map_of_mem σ.val h1_right
  case forall_ x phi phi_ih =>
    unfold NoMetaVarAndAllFreeInList at h1

    unfold sub
    unfold NoMetaVarAndAllFreeInList
    simp only [← List.map_cons]
    exact phi_ih (x :: vs) h1
  case def_ X xs =>
    unfold sub
    unfold NoMetaVarAndAllFreeInList
    exact List.map_subset σ.val h1


theorem sub_meta_id_preserves_is_meta_var_or_all_def_in_env
  (F : Formula)
  (E : Env)
  (σ : Instantiation)
  (h1 : IsMetaVarOrAllDefInEnv E F) :
  IsMetaVarOrAllDefInEnv E (sub σ Formula.meta_var_ F) :=
  by
  induction F
  case meta_var_ X =>
    unfold sub
    unfold IsMetaVarOrAllDefInEnv
    simp only
  case pred_ X xs =>
    unfold sub
    unfold IsMetaVarOrAllDefInEnv
    simp only
  case eq_ x y =>
    unfold sub
    unfold IsMetaVarOrAllDefInEnv
    simp only
  case true_ =>
    unfold sub
    unfold IsMetaVarOrAllDefInEnv
    simp only
  case not_ phi phi_ih =>
    unfold IsMetaVarOrAllDefInEnv at h1

    unfold sub
    unfold IsMetaVarOrAllDefInEnv
    exact phi_ih h1
  case imp_ phi psi phi_ih psi_ih =>
    unfold IsMetaVarOrAllDefInEnv at h1

    unfold sub
    unfold IsMetaVarOrAllDefInEnv
    cases h1
    case intro h1_left h1_right =>
    constructor
    · exact phi_ih h1_left
    · exact psi_ih h1_right
  case forall_ x phi phi_ih =>
    unfold IsMetaVarOrAllDefInEnv at h1

    unfold sub
    unfold IsMetaVarOrAllDefInEnv
    exact phi_ih h1
  case def_ X xs =>
    unfold IsMetaVarOrAllDefInEnv at h1

    unfold sub
    unfold IsMetaVarOrAllDefInEnv
    simp
    exact h1


theorem well_formed_env_has_no_dup
  (E : Env)
  (h1 : E.WellFormed) :
  E.Nodup :=
  by
  induction E
  case nil =>
    unfold Env.Nodup
    simp
  case cons hd tl ih =>
    unfold Env.Nodup at ih

    unfold Env.WellFormed at h1

    cases h1
    case intro h1_left h1_right =>
      cases h1_right
      case intro h1_right_left h1_right_right =>
        unfold Env.Nodup
        simp
        constructor
        · exact h1_left
        · exact ih h1_right_right


theorem concat_env_preserves_is_meta_var_or_all_def_in_env
  (E E' : Env)
  (F : Formula)
  (h1 : ∃ E1 : Env, E' = E1 ++ E)
  (h2 : IsMetaVarOrAllDefInEnv E F) :
  IsMetaVarOrAllDefInEnv E' F :=
  by
  induction E generalizing F
  all_goals
    induction F
    case meta_var_ X =>
      unfold IsMetaVarOrAllDefInEnv
      simp only
    case pred_ X xs =>
      unfold IsMetaVarOrAllDefInEnv
      simp only
    case eq_ x y =>
      unfold IsMetaVarOrAllDefInEnv
      simp only
    case true_ =>
      unfold IsMetaVarOrAllDefInEnv
      simp only
    case not_ phi phi_ih =>
      unfold IsMetaVarOrAllDefInEnv at h2

      unfold IsMetaVarOrAllDefInEnv
      exact phi_ih h2
    case imp_ phi psi phi_ih psi_ih =>
      unfold IsMetaVarOrAllDefInEnv at h2

      unfold IsMetaVarOrAllDefInEnv
      cases h2
      case intro h2_left h2_right =>
      constructor
      · exact phi_ih h2_left
      · exact psi_ih h2_right
    case forall_ x phi phi_ih =>
      unfold IsMetaVarOrAllDefInEnv at h2

      unfold IsMetaVarOrAllDefInEnv
      exact phi_ih h2

  case nil.def_ X xs =>
    unfold IsMetaVarOrAllDefInEnv at h2
    simp at h2
  case cons.def_ E_hd E_tl E_ih X xs =>
    unfold IsMetaVarOrAllDefInEnv at h2

    apply Exists.elim h1
    intro E1 h1_1

    apply Exists.elim h2
    intro d h2_1

    cases h2_1
    case intro h2_1_left h2_1_right =>
      simp at h2_1_left
      cases h2_1_left
      case inl c1 =>
        unfold IsMetaVarOrAllDefInEnv
        apply Exists.intro E_hd
        simp only [h1_1]
        constructor
        · simp
        · simp only [← c1]
          exact h2_1_right
      case inr c1 =>
        apply E_ih
        · apply Exists.intro (E1 ++ [E_hd])
          simp
          exact h1_1

        · unfold IsMetaVarOrAllDefInEnv
          apply Exists.intro d
          constructor
          · exact c1
          · exact h2_1_right


theorem def_in_well_formed_env_is_meta_var_or_all_def_in_env
  (E : Env)
  (d : Definition)
  (h1 : E.WellFormed)
  (h2 : d ∈ E) :
  IsMetaVarOrAllDefInEnv E d.F :=
  by
  induction E
  case nil =>
    simp at h2
  case cons hd tl ih =>
    unfold Env.WellFormed at h1

    simp at h2

    cases h1
    case intro h1_left h1_right =>
      cases h1_right
      case intro h1_right_left h1_right_right =>
        apply concat_env_preserves_is_meta_var_or_all_def_in_env tl (hd :: tl)
        · apply Exists.intro [hd]
          simp
        · cases h2
          case _ c1 =>
            subst c1
            exact h1_right_left
          case _ c1 =>
            exact ih h1_right_right c1


theorem holds_coincide_var
  (D : Type)
  (I : Interpretation D)
  (V V' : Valuation D)
  (M : MetaValuation D)
  (E : Env)
  (F : Formula)
  (vs : List VarName)
  (h1 : NoMetaVarAndAllFreeInList vs F)
  (h2 : ∀ v : VarName, v ∈ vs → V v = V' v) :
  Holds D I V M E F ↔ Holds D I V' M E F :=
  by
  induction E generalizing F vs V V'
  all_goals
    induction F generalizing vs V V'
    case meta_var_ X =>
      unfold NoMetaVarAndAllFreeInList at h1

      contradiction
    case pred_ X xs =>
      unfold NoMetaVarAndAllFreeInList at h1

      simp only [Holds]
      congr! 1
      simp only [List.map_eq_map_iff]
      tauto
    case eq_ x y =>
      unfold NoMetaVarAndAllFreeInList at h1

      cases h1
      case intro h1_left h1_right =>
        simp only [Holds]
        congr! 1
        · exact h2 x h1_left
        · exact h2 y h1_right
    case true_ =>
      simp only [Holds]
    case not_ phi phi_ih =>
      unfold NoMetaVarAndAllFreeInList at h1

      simp only [Holds]
      congr! 1
      exact phi_ih V V' vs h1 h2
    case imp_ phi psi phi_ih psi_ih =>
      unfold NoMetaVarAndAllFreeInList at h1

      simp only [Holds]
      cases h1
      case intro h1_left h1_right =>
        congr! 1
        · exact phi_ih V V' vs h1_left h2
        · exact psi_ih V V' vs h1_right h2
    case forall_ x phi phi_ih =>
      unfold NoMetaVarAndAllFreeInList at h1

      simp only [Holds]
      apply forall_congr'
      intro a
      apply phi_ih
      · exact h1
      · intro v a1
        unfold Function.updateITE
        split_ifs
        case _ c1 =>
          rfl
        case _ c1 =>
          simp at a1
          tauto

  case nil.def_ X xs =>
    simp only [Holds]

  case cons.def_ E_hd E_tl E_ih X xs =>
    unfold NoMetaVarAndAllFreeInList at h1

    simp only [Holds]
    split_ifs
    case _ c1 =>
      apply E_ih (Function.updateListITE V E_hd.args (List.map V xs)) (Function.updateListITE V' E_hd.args (List.map V' xs)) E_hd.F E_hd.args E_hd.nf
      intro v a1
      apply Function.updateListITE_fun_coincide_mem_eq_len
      · tauto
      · exact a1
      · tauto
    case _ c1 =>
      apply E_ih V V' (def_ X xs) vs
      · unfold NoMetaVarAndAllFreeInList
        exact h1
      · exact h2


theorem holds_coincide_meta_var
  (D : Type)
  (I : Interpretation D)
  (V : Valuation D)
  (M M' : MetaValuation D)
  (E : Env)
  (F : Formula)
  (h1 : ∀ (V' : Valuation D) (X : MetaVarName), X ∈ F.metaVarSet → (M X V' ↔ M' X V')) :
    Holds D I V M E F ↔ Holds D I V M' E F :=
  by
  induction E generalizing F V M M'
  all_goals
    induction F generalizing V M M'
    case meta_var_ X =>
      unfold Formula.metaVarSet at h1
      simp at h1

      simp only [Holds]
      exact h1 V
    case pred_ X xs =>
      simp only [Holds]
    case eq_ x y =>
      simp only [Holds]
    case true_ =>
      simp only [Holds]
    case not_ phi phi_ih =>
      unfold Formula.metaVarSet at h1

      simp only [Holds]
      congr! 1
      exact phi_ih V M M' h1
    case imp_ phi psi phi_ih psi_ih =>
      unfold Formula.metaVarSet at h1
      simp at h1

      simp only [Holds]
      congr! 1
      · apply phi_ih
        intro V' X a1
        apply h1
        left
        exact a1
      · apply psi_ih
        intro V' X a1
        apply h1
        right
        exact a1
    case forall_ x phi phi_ih =>
      unfold Formula.metaVarSet at h1

      simp only [Holds]
      apply forall_congr'
      intro a
      exact phi_ih (Function.updateITE V x a) M M' h1

  case nil.def_ X xs =>
    simp only [Holds]

  case cons.def_ E_hd E_tl E_ih X xs =>
    simp only [Holds]
    split_ifs
    · apply E_ih
      simp only [no_meta_var_imp_meta_var_set_is_empty E_hd.F E_hd.args E_hd.nf]
      simp
    · apply E_ih
      unfold Formula.metaVarSet
      simp


theorem holds_coincide_meta_var_no_meta_var
  (D : Type)
  (I : Interpretation D)
  (V : Valuation D)
  (M M' : MetaValuation D)
  (E : Env)
  (F : Formula)
  (h1 : F.metaVarSet = ∅) :
  Holds D I V M E F ↔ Holds D I V M' E F :=
  by
  apply holds_coincide_meta_var
  simp only [h1]
  simp


theorem def_holds_imp_def_in_env
  (D : Type)
  (I : Interpretation D)
  (V : Valuation D)
  (M : MetaValuation D)
  (E : Env)
  (name : DefName)
  (args : List VarName)
  (h1 : Holds D I V M E (def_ name args)) :
  ∃ d : Definition, d ∈ E ∧ name = d.name ∧ args.length = d.args.length :=
  by
  induction E
  case nil =>
    simp only [Holds] at h1
  case cons E_hd E_tl E_ih =>
    simp only [Holds] at h1

    split_ifs at h1
    case _ c1 =>
      apply Exists.intro E_hd
      simp
      exact c1
    case _ c1 =>
      specialize E_ih h1
      apply Exists.elim E_ih
      intro d E_ih_1
      cases E_ih_1
      case intro E_ih_1_left E_ih_1_right =>
        apply Exists.intro d
        constructor
        · simp
          right
          exact E_ih_1_left
        · exact E_ih_1_right


example
  (D : Type)
  (I : Interpretation D)
  (V : Valuation D)
  (M : MetaValuation D)
  (E E' : Env)
  (name : DefName)
  (args : List VarName)
  (h1 : ∃ E1 : Env, E' = E1 ++ E)
  (h2 : E'.Nodup)
  (h3 : Holds D I V M E (def_ name args)) :
  Holds D I V M E' (def_ name args) :=
  by
  apply Exists.elim h1
  intro E1 h1_1
  clear h1

  unfold Env.Nodup at h2

  subst h1_1
  induction E1
  case nil =>
    simp
    exact h3
  case cons E1_hd E1_tl E1_ih =>
    simp at h2

    cases h2
    case intro h2_left h2_right =>
      specialize E1_ih h2_right
      simp
      simp only [Holds]
      split_ifs
      case _ c1 =>
        have s1 : ∃ d : Definition, d ∈ E1_tl ++ E ∧ name = d.name ∧ args.length = d.args.length :=
        def_holds_imp_def_in_env D I V M (E1_tl ++ E) name args E1_ih

        apply Exists.elim s1
        intro d s1_1
        cases s1_1
        case intro s1_1_left s1_1_right =>
          simp at s1_1_left
          cases s1_1_right
          case intro s1_1_right_left s1_1_right_right =>
            cases c1
            case intro c1_left c1_right =>
              exfalso
              apply h2_left d s1_1_left
              · simp only [← c1_left]
                exact s1_1_right_left
              · simp only [← c1_right]
                exact s1_1_right_right
      case _ c1 =>
        exact E1_ih


theorem holds_coincide_env
  (D : Type)
  (I : Interpretation D)
  (V : Valuation D)
  (M : MetaValuation D)
  (E E' : Env)
  (F : Formula)
  (h1 : ∃ E1 : Env, E' = E1 ++ E)
  (h2 : IsMetaVarOrAllDefInEnv E F)
  (h3 : E'.Nodup) :
  Holds D I V M E' F ↔ Holds D I V M E F :=
  by
  induction F generalizing V
  case meta_var_ X =>
    simp only [Holds]
  case pred_ X xs =>
    simp only [Holds]
  case eq_ x y =>
    simp only [Holds]
  case true_ =>
    simp only [Holds]
  case not_ phi phi_ih =>
    unfold IsMetaVarOrAllDefInEnv at h2

    simp only [Holds]
    congr! 1
    exact phi_ih V h2
  case imp_ phi psi phi_ih psi_ih =>
    unfold IsMetaVarOrAllDefInEnv at h2

    cases h2
    case intro h2_left h2_right =>
      simp only [Holds]
      congr! 1
      · exact phi_ih V h2_left
      · exact psi_ih V h2_right
  case forall_ x phi phi_ih =>
    unfold IsMetaVarOrAllDefInEnv at h2

    simp only [Holds]
    apply forall_congr'
    intro a
    exact phi_ih (Function.updateITE V x a) h2
  case def_ X xs =>
    apply Exists.elim h1
    intro E1 h1_1
    clear h1

    unfold IsMetaVarOrAllDefInEnv at h2
    apply Exists.elim h2
    intro a h2_1
    clear h2

    unfold Env.Nodup at h3

    cases h2_1
    case intro h2_1_left h2_1_right =>
      cases h2_1_right
      case intro h2_1_right_left h2_1_right_right =>
        subst h1_1

        induction E1
        case nil =>
          simp
        case cons E1_hd E1_tl E1_ih =>
          simp at h3
          cases h3
          case intro h3_left h3_right =>
            simp
            simp only [Holds]
            split_ifs
            case _ c1 =>
              cases c1
              case intro c1_left c1_right =>
                exfalso
                apply h3_left a
                · right
                  exact h2_1_left
                · simp only [← h2_1_right_left]
                  simp only [c1_left]
                · simp only [← h2_1_right_right]
                  simp only [c1_right]
            case _ c1 =>
              exact E1_ih h3_right


theorem holds_sub
  (D : Type)
  (I : Interpretation D)
  (V : Valuation D)
  (M : MetaValuation D)
  (E : Env)
  (σ : Instantiation)
  (σ' : VarName → VarName)
  (τ : MetaInstantiation)
  (F : Formula)
  (h1 : IsMetaVarOrAllDefInEnv E F)
  (h2 : σ.1 ∘ σ' = id ∧ σ' ∘ σ.1 = id) :
  Holds D I (V ∘ σ.1) (fun (X' : MetaVarName) (V' : Valuation D) => Holds D I (V' ∘ σ') M E (τ X')) E F ↔
    Holds D I V M E (sub σ τ F) :=
  by
  induction F generalizing V
  case meta_var_ X =>
    cases h2
    case intro h2_left h2_right =>
      unfold sub
      simp only [Holds]
      simp only [Function.comp.assoc]
      simp only [h2_left]
      simp only [Function.comp_id]
  case pred_ X xs =>
    unfold sub
    simp only [Holds]
    simp
  case eq_ x y =>
    unfold sub
    simp only [Holds]
    simp
  case true_ =>
    unfold sub
    simp only [Holds]
  case not_ phi phi_ih =>
    unfold IsMetaVarOrAllDefInEnv at h1

    unfold sub
    simp only [Holds]
    congr! 1
    exact phi_ih V h1
  case imp_ phi psi phi_ih psi_ih =>
    unfold IsMetaVarOrAllDefInEnv at h1

    cases h1
    case intro h1_left h1_right =>
      unfold sub
      simp only [Holds]
      congr! 1
      · exact phi_ih V h1_left
      · exact psi_ih V h1_right
  case forall_ x phi phi_ih =>
    unfold IsMetaVarOrAllDefInEnv at h1

    cases h2
    case intro h2_left h2_right =>
      unfold sub
      simp only [Holds]
      apply forall_congr'
      intro a

      have s1 : Function.updateITE V (σ.val x) a ∘ σ.val = Function.updateITE (V ∘ σ.val) x a
      apply Function.updateITE_comp_right_injective
      apply Instantiation.is_injective

      simp only [← s1]

      exact phi_ih (Function.updateITE V (σ.val x) a) h1

  case def_ X xs =>
    induction E
    case nil =>
      unfold IsMetaVarOrAllDefInEnv at h1
      simp at h1
    case cons E_hd E_tl E_ih =>
      unfold IsMetaVarOrAllDefInEnv at E_ih

      have s1 : E_hd.F.metaVarSet = ∅ :=
        no_meta_var_imp_meta_var_set_is_empty E_hd.F E_hd.args E_hd.nf

      unfold sub
      simp only [Holds]
      simp

      split_ifs
      case _ c1 =>
        cases c1
        case intro c1_left c1_right =>
          have s2 : Holds D I (Function.updateListITE (V ∘ σ.val) E_hd.args (List.map (V ∘ σ.val) xs)) M E_tl E_hd.F ↔ Holds D I (Function.updateListITE V E_hd.args (List.map (V ∘ σ.val) xs)) M E_tl E_hd.F
          apply holds_coincide_var D I (Function.updateListITE (V ∘ σ.val) E_hd.args (List.map (V ∘ σ.val) xs)) (Function.updateListITE V E_hd.args (List.map (V ∘ σ.val) xs)) M E_tl E_hd.F E_hd.args E_hd.nf
          intro v a1
          apply Function.updateListITE_mem_eq_len
          · exact a1
          · simp
            simp only [c1_right]

          simp only [← s2]
          apply holds_coincide_meta_var_no_meta_var
          exact s1
      case _ c1 =>
        unfold IsMetaVarOrAllDefInEnv at h1
        simp at h1

        cases h1
        case inl c2 =>
          contradiction
        case inr c2 =>
          unfold sub at E_ih
          simp only [← E_ih c2]
          apply holds_coincide_meta_var
          unfold Formula.metaVarSet
          simp


example
  (D : Type)
  (I : Interpretation D)
  (M : MetaValuation D)
  (E : Env)
  (F : Formula)
  (v : VarName) :
  IsNotFree D I M E F v ↔
    ∀ V V' : Valuation D,
      (∀ y : VarName, ¬ y = v → V y = V' y) →
        (Holds D I V M E F ↔ Holds D I V' M E F) :=
  by
  unfold IsNotFree
  constructor
  · intro a1 V V' a2
    simp only [a1 V (V' v)]
    simp only [Function.updateITE_coincide V V' v a2]
  · intro a1 V d
    apply a1
    intro a' a2
    unfold Function.updateITE
    simp only [if_neg a2]


theorem not_free_imp_is_not_free
  (D : Type)
  (I : Interpretation D)
  (M : MetaValuation D)
  (E : Env)
  (F : Formula)
  (Γ : List (VarName × MetaVarName))
  (v : VarName)
  (h1 : NotFree Γ v F)
  (h2 : ∀ X : MetaVarName, (v, X) ∈ Γ → IsNotFree D I M E (meta_var_ X) v) :
  IsNotFree D I M E F v :=
  by
  induction F
  case meta_var_ X =>
    unfold NotFree at h1

    exact h2 X h1
  case pred_ X xs =>
    unfold NotFree at h1

    unfold IsNotFree
    simp only [Holds]
    intro V d
    congr! 1
    apply List.map_congr
    intro x a1

    have s1 : ¬ x = v
    intro contra
    subst contra
    contradiction

    unfold Function.updateITE
    simp only [if_neg s1]
  case eq_ x y =>
    unfold NotFree at h1

    unfold IsNotFree
    simp only [Holds]
    intro V d
    cases h1
    case intro h1_left h1_right =>
      simp only [Function.updateITE]
      simp only [if_neg h1_left]
      simp only [if_neg h1_right]
  case true_ =>
    unfold IsNotFree
    intro V d
    simp only [Holds]
  case not_ phi phi_ih =>
    unfold NotFree at h1

    unfold IsNotFree at phi_ih

    unfold IsNotFree
    intro V d
    simp only [Holds]
    congr! 1
    exact phi_ih h1 V d
  case imp_ phi psi phi_ih psi_ih =>
    unfold NotFree at h1

    unfold IsNotFree at phi_ih
    unfold IsNotFree at psi_ih

    unfold IsNotFree
    intro V d
    simp only [Holds]
    cases h1
    case intro h1_left h1_right =>
      congr! 1
      · exact phi_ih h1_left V d
      · exact psi_ih h1_right V d
  case forall_ x phi phi_ih =>
    unfold NotFree at h1

    unfold IsNotFree at phi_ih

    unfold IsNotFree
    intro V d
    simp only [Holds]
    apply forall_congr'
    intro d'
    by_cases c1 : x = v
    · cases h1
      case _ c2 =>
        subst c1
        simp only [Function.updateITE_idem]
      case _ c2 =>
        subst c1
        simp only [Function.updateITE_idem]
    · cases h1
      case _ c2 =>
        contradiction
      case _ c2 =>
        simp only [← Function.updateITE_comm V x v d d' c1]
        exact phi_ih c2 (Function.updateITE V x d') d
  case def_ X xs =>
    induction E
    case nil =>
      unfold IsNotFree
      intro V d
      simp only [Holds]
    case cons E_hd E_tl E_ih =>
      unfold NotFree at h1

      unfold IsNotFree at h2
      simp only [Holds] at h2

      unfold IsNotFree at E_ih
      simp only [Holds] at E_ih

      unfold IsNotFree
      simp only [Holds]

      intro V a

      split_ifs
      case _ c1 =>
        apply holds_coincide_var D I (Function.updateListITE V E_hd.args (List.map V xs)) (Function.updateListITE (Function.updateITE V v a) E_hd.args (List.map (Function.updateITE V v a) xs)) M E_tl E_hd.F E_hd.args E_hd.nf
        · intro v' a1
          apply Function.updateListITE_map_updateIte V (Function.updateITE V v a)
          · intro y a2 contra
            subst contra
            contradiction
          · cases c1
            case intro c1_left c1_right =>
            simp only [c1_right]
          · exact a1
      case _ c1 =>
        exact E_ih h2 V a


theorem lem_1
  (D : Type)
  (I : Interpretation D)
  (M : MetaValuation D)
  (E : Env)
  (Γ Γ' : List (VarName × MetaVarName))
  (σ : Instantiation)
  (σ' : VarName → VarName)
  (τ : MetaInstantiation)
  (h1 : σ.1 ∘ σ' = id ∧ σ' ∘ σ.1 = id)
  (h2 : ∀ (v : VarName) (X : MetaVarName), (v, X) ∈ Γ' → IsNotFree D I M E (meta_var_ X) v)
  (h3 : ∀ (v : VarName) (X : MetaVarName), (v, X) ∈ Γ → NotFree Γ' (σ.1 v) (τ X)) :
  ∀ (v : VarName) (X : MetaVarName),
    (v, X) ∈ Γ →
      IsNotFree D I (fun (X : MetaVarName) (V' : Valuation D) => Holds D I (V' ∘ σ') M E (τ X)) E (meta_var_ X) v :=
  by
  intro v X a1
  unfold IsNotFree
  simp only [Holds]
  intro V d
  cases h1
  case intro h1_left h1_right =>
    simp only [Function.updateITE_comp_right σ' σ.1 V v d h1_left h1_right]
    apply not_free_imp_is_not_free D I M E (τ X) Γ' (σ.1 v)
    · exact h3 v X a1
    · intro X' a2
      exact h2 (σ.1 v) X' a2


theorem lem_2_a
  (E : Env)
  (σ : Instantiation)
  (τ : MetaInstantiation)
  (F : Formula)
  (h1 : IsMetaVarOrAllDefInEnv E F)
  (h2 : ∀ X : MetaVarName, X ∈ F.metaVarSet → IsMetaVarOrAllDefInEnv E (τ X)) :
  IsMetaVarOrAllDefInEnv E (sub σ τ F) :=
  by
  induction F
  case meta_var_ X =>
    unfold Formula.metaVarSet at h2
    simp at h2

    unfold sub
    exact h2
  case pred_ X xs =>
    unfold sub
    unfold IsMetaVarOrAllDefInEnv
    simp only
  case eq_ x y =>
    unfold sub
    unfold IsMetaVarOrAllDefInEnv
    simp only
  case true_ =>
    unfold sub
    unfold IsMetaVarOrAllDefInEnv
    simp only
  case not_ phi phi_ih =>
    unfold IsMetaVarOrAllDefInEnv at h1

    unfold Formula.metaVarSet at h2

    unfold sub
    unfold IsMetaVarOrAllDefInEnv
    exact phi_ih h1 h2
  case imp_ phi psi phi_ih psi_ih =>
    unfold IsMetaVarOrAllDefInEnv at h1

    unfold Formula.metaVarSet at h2
    simp at h2

    unfold sub
    unfold IsMetaVarOrAllDefInEnv
    cases h1
    case intro h1_left h1_right =>
      constructor
      · apply phi_ih h1_left
        intro X a1
        apply h2
        left
        exact a1
      · apply psi_ih h1_right
        intro X a1
        apply h2
        right
        exact a1
  case forall_ x phi phi_ih =>
    unfold IsMetaVarOrAllDefInEnv at h1

    unfold Formula.metaVarSet at h2

    unfold sub
    unfold IsMetaVarOrAllDefInEnv
    exact phi_ih h1 h2
  case def_ X xs =>
    unfold IsMetaVarOrAllDefInEnv at h1

    unfold sub
    unfold IsMetaVarOrAllDefInEnv
    simp
    exact h1


theorem lem_2_b
  (E : Env)
  (σ : Instantiation)
  (τ : MetaInstantiation)
  (F : Formula)
  (h1 : IsMetaVarOrAllDefInEnv E (sub σ τ F)) :
  IsMetaVarOrAllDefInEnv E F :=
  by
  induction F
  case meta_var_ X =>
    unfold IsMetaVarOrAllDefInEnv
    simp only
  case pred_ X xs =>
    unfold IsMetaVarOrAllDefInEnv
    simp only
  case eq_ x y =>
    unfold IsMetaVarOrAllDefInEnv
    simp only
  case true_ =>
    unfold IsMetaVarOrAllDefInEnv
    simp only
  case not_ phi phi_ih =>
    unfold sub at h1
    unfold IsMetaVarOrAllDefInEnv at h1

    unfold IsMetaVarOrAllDefInEnv
    exact phi_ih h1
  case imp_ phi psi phi_ih psi_ih =>
    unfold sub at h1
    unfold IsMetaVarOrAllDefInEnv at h1

    unfold IsMetaVarOrAllDefInEnv
    cases h1
    case intro h1_left h1_right =>
    constructor
    · exact phi_ih h1_left
    · exact psi_ih h1_right
  case forall_ x phi phi_ih =>
    unfold sub at h1
    unfold IsMetaVarOrAllDefInEnv at h1

    unfold IsMetaVarOrAllDefInEnv
    exact phi_ih h1
  case def_ X xs =>
    unfold sub at h1
    unfold IsMetaVarOrAllDefInEnv at h1
    simp at h1

    unfold IsMetaVarOrAllDefInEnv
    exact h1


theorem is_proof_imp_is_meta_var_or_all_def_in_env
  (E : Env)
  (Γ : List (VarName × MetaVarName))
  (Δ : List Formula)
  (F : Formula)
  (h1 : IsProof E Γ Δ F) :
  IsMetaVarOrAllDefInEnv E F :=
  by
  induction h1
  case hyp h1_Γ h1_Δ h1_phi h1_1 h1_2 =>
    exact h1_1
  case mp h1_Γ h1_Δ h1_phi h1_psi h1_1 h1_2 h1_ih_1 h1_ih_2 =>
    unfold IsMetaVarOrAllDefInEnv at h1_ih_2

    cases h1_ih_2
    case intro h1_ih_2_left h1_ih_2_right =>
      exact h1_ih_2_right
  case prop_1 h1_Γ h1_Δ h1_phi h1_psi h1_1 h1_2 =>
    repeat first | constructor | assumption
  case prop_2 h1_Γ h1_Δ h1_phi h1_psi h1_chi h1_1 h1_2 h1_3 =>
    repeat first | constructor | assumption
  case prop_3 h1_Γ h1_Δ h1_phi h1_psi h1_1 h1_2 =>
    repeat first | constructor | assumption
  case gen h1_Γ h1_Δ h1_phi h1_x h1_1 h1_ih =>
    repeat first | constructor | assumption
  case pred_1 h1_Γ h1_Δ h1_phi h1_psi h1_x h1_1 h1_2 =>
    repeat first | constructor | assumption
  case pred_2 h1_Γ h1_Δ h1_phi h1_x h1_1 h1_2 =>
    repeat first | constructor | assumption
  case eq_1 h1_Γ h1_Δ h1_x h1_y h1_1 =>
    unfold exists_
    repeat first | constructor | assumption
  case eq_2 h1_Γ h1_Δ h1_x h1_y h1_z =>
    unfold IsMetaVarOrAllDefInEnv
    repeat first | constructor | assumption
  case eq_3 h1_Γ h1_Δ h1_n h1_name h1_xs h1_ys =>
    sorry
  case thm h1_Γ h1_Γ' h1_Δ h1_Δ' h1_phi h1_σ h1_τ h1_1 h1_2 h1_3 h1_4 h1_ih_1 h1_ih_2 =>
    exact lem_2_a E h1_σ h1_τ h1_phi h1_ih_2 h1_1
  case conv h1_Γ h1_Δ h1_phi h1_phi' h1_1 h1_2 h1_3 h1_ih =>
    exact h1_1


theorem lem_4
  (D : Type)
  (I : Interpretation D)
  (V : Valuation D)
  (M : MetaValuation D)
  (E : Env)
  (d : Definition)
  (name : DefName)
  (args : List VarName)
  (h1 : E.WellFormed)
  (h2 : d ∈ E)
  (h3 : name = d.name ∧ args.length = d.args.length) :
  Holds D I (Function.updateListITE V d.args (List.map V args)) M E d.F ↔ Holds D I V M E (def_ name args) :=
  by
  induction E
  case nil =>
    simp at h2
  case cons hd tl ih =>
    have s1 : Env.Nodup (hd :: tl) := well_formed_env_has_no_dup (hd :: tl) h1

    have s2 : ∃ E1 : Env, (hd :: tl) = E1 ++ tl
    apply Exists.intro [hd]
    simp

    unfold Env.WellFormed at h1

    simp at h2

    cases h1
    case intro h1_left h1_right =>
      cases h1_right
      case intro h1_right_left h1_right_right =>
        simp only [Holds]
        split_ifs
        case _ c1 =>
          cases h2
          case inl c2 =>
            subst c2
            exact holds_coincide_env D I (Function.updateListITE V d.args (List.map V args)) M tl (d :: tl) d.F s2 h1_right_left s1
          case inr c2 =>
            cases h3
            case intro h3_left h3_right =>
              cases c1
              case intro c1_left c1_right =>
                exfalso
                apply h1_left d c2
                · simp only [← c1_left]
                  exact h3_left
                · simp only [← c1_right]
                  exact h3_right
        case _ c1 =>
          cases h2
          case inl c2 =>
            subst c2
            simp at c1
            cases h3
            case intro h3_left h3_right =>
              exfalso
              exact c1 h3_left h3_right
          case inr c2 =>
            specialize ih h1_right_right c2
            simp only [← ih]
            apply holds_coincide_env D I (Function.updateListITE V d.args (List.map V args)) M tl (hd :: tl) d.F s2
            apply def_in_well_formed_env_is_meta_var_or_all_def_in_env tl d h1_right_right c2
            exact s1


theorem holds_conv
  (D : Type)
  (I : Interpretation D)
  (V : Valuation D)
  (M : MetaValuation D)
  (E : Env)
  (F F' : Formula)
  (h1 : E.WellFormed)
  (h2 : IsConv E F F') :
  Holds D I V M E F ↔ Holds D I V M E F' :=
  by
  induction h2 generalizing V
  case conv_refl h2_phi =>
    rfl
  case conv_symm h2_phi h2_phi' _ h2_ih =>
    symm
    exact h2_ih V
  case conv_trans h2_phi h2_phi' h2_phi'' _ _ h2_ih_1 h2_ih_2 =>
    trans Holds D I V M E h2_phi'
    exact h2_ih_1 V
    exact h2_ih_2 V
  case conv_not h2_phi h2_phi' _ h2_ih =>
    simp only [Holds]
    congr! 1
    exact h2_ih V
  case conv_imp h2_phi h2_phi' h2_psi h2_psi' _ _ h2_ih_1 h2_ih_2 =>
    simp only [Holds]
    congr! 1
    · exact h2_ih_1 V
    · exact h2_ih_2 V
  case conv_forall h2_x h2_phi h2_phi' _ h2_ih =>
    simp only [Holds]
    apply forall_congr'
    intro a
    exact h2_ih (Function.updateITE V h2_x a)
  case conv_unfold d σ h2 =>
    obtain ⟨σ', a1⟩ := σ.2
    have s1 : IsMetaVarOrAllDefInEnv E d.F := def_in_well_formed_env_is_meta_var_or_all_def_in_env E d h1 h2

    simp only [← holds_sub D I V M E σ σ' meta_var_ d.F s1 a1]
    clear s1

    have s2 : d.name = d.name ∧ (List.map σ.val d.args).length = d.args.length
    simp
    simp only [← lem_4 D I V M E d d.name (List.map σ.val d.args) h1 h2 s2]
    clear s2

    have s3 : d.F.metaVarSet = ∅ := no_meta_var_imp_meta_var_set_is_empty d.F d.args d.nf

    simp only [holds_coincide_meta_var_no_meta_var D I (V ∘ σ.val) (fun (X' : MetaVarName) (V' : Valuation D) => Holds D I (V' ∘ σ') M E (meta_var_ X')) M E d.F s3]
    clear s3

    apply holds_coincide_var D I (Function.updateListITE V d.args (List.map V (List.map σ.val d.args))) (V ∘ σ.val) M E d.F d.args d.nf
    intro v a2
    simp
    exact Function.updateListITE_map_mem V (V ∘ σ.val) d.args v a2


theorem holds_is_proof
  (D : Type)
  (I : Interpretation D)
  (M : MetaValuation D)
  (E : Env)
  (Γ : List (VarName × MetaVarName))
  (Δ : List Formula)
  (F : Formula)
  (h1 : IsProof E Γ Δ F)
  (h2 : E.WellFormed)
  (nf : ∀ (v : VarName) (X : MetaVarName), (v, X) ∈ Γ → IsNotFree D I M E (meta_var_ X) v)
  (hyp : ∀ (F : Formula) (V : Valuation D), F ∈ Δ → Holds D I V M E F) :
    ∀ V : Valuation D, Holds D I V M E F :=
  by
  induction h1 generalizing M
  case hyp h1_Γ h1_Δ h1_phi h1_1 h1_2 =>
    intro V
    exact hyp h1_phi V h1_2
  case mp h1_Γ h1_Δ h1_phi h1_psi h1_1 h1_2 h1_ih_1 h1_ih_2 =>
    simp only [Holds] at h1_ih_2
    intro V
    exact h1_ih_2 M nf hyp V (h1_ih_1 M nf hyp V)
  case prop_1 h1_Γ h1_Δ h1_phi h1_psi h1_1 h1_2 =>
    simp only [Holds]
    intro V a1 a2
    exact a1
  case prop_2 h1_Γ h1_Δ h1_phi h1_psi h1_chi h1_1 h1_2 h1_3 =>
    simp only [Holds]
    intro V a1 a2 a3
    apply a1 a3
    exact a2 a3
  case prop_3 h1_Γ h1_Δ h1_phi h1_psi h1_1 h1_2 =>
    simp only [Holds]
    intro V a1 a2
    by_contra contra
    exact a1 contra a2
  case gen h1_Γ h1_Δ h1_phi h1_x h1_1 h1_ih =>
    simp only [Holds]
    intro V d
    exact h1_ih M nf hyp (Function.updateITE V h1_x d)
  case pred_1 h1_Γ h1_Δ h1_phi h1_psi h1_x h1_1 h1_2 =>
    simp only [Holds]
    intro V a1 a2 d
    apply a1 d
    exact a2 d
  case pred_2 h1_Γ h1_Δ h1_phi h1_x h1_1 h1_2 =>
    have s1 : IsNotFree D I M E h1_phi h1_x
    apply not_free_imp_is_not_free D I M E h1_phi h1_Γ h1_x h1_2
    exact nf h1_x

    simp only [Holds]
    intro V a1 a
    unfold IsNotFree at s1
    simp only [← s1 V a]
    exact a1
  case eq_1 h1_Γ h1_Δ h1_x h1_y h1_1 =>
    unfold exists_
    simp only [Holds]
    simp
    intro V
    apply Exists.intro (V h1_y)
    unfold Function.updateITE
    simp
  case eq_2 h1_Γ h1_Δ h1_x h1_y h1_z =>
    simp only [Holds]
    intro V a1 a2
    trans V h1_x
    · simp only [a1]
    · exact a2
  case eq_3 h1_Γ h1_Δ h1_n h1_name h1_xs h1_ys =>
    sorry
  case thm h1_Γ h1_Γ' h1_Δ h1_Δ' h1_phi h1_σ h1_τ h1_1 h1_2 h1_3 h1_4 h1_ih_1 h1_ih_2 =>
    obtain ⟨σ', a1⟩ := h1_σ.2

    have s1 : IsMetaVarOrAllDefInEnv E h1_phi := is_proof_imp_is_meta_var_or_all_def_in_env E h1_Γ h1_Δ h1_phi h1_4

    intro V
    simp only [← holds_sub D I V M E h1_σ σ' h1_τ h1_phi s1 a1]
    apply h1_ih_2
    · intro v X a2
      exact lem_1 D I M E h1_Γ h1_Γ' h1_σ σ' h1_τ a1 nf h1_2 v X a2
    · intro psi V' a2
      have s2 : IsMetaVarOrAllDefInEnv E psi
      apply lem_2_b E h1_σ h1_τ
      apply is_proof_imp_is_meta_var_or_all_def_in_env E h1_Γ' h1_Δ' (sub h1_σ h1_τ psi)
      exact h1_3 psi a2

      have s3 : ∀ V'' : Valuation D, Holds D I (V'' ∘ h1_σ.val) (fun (X' : MetaVarName) (V' : Valuation D) => Holds D I (V' ∘ σ') M E (h1_τ X')) E psi
      intro V''
      simp only [holds_sub D I V'' M E h1_σ σ' h1_τ psi s2 a1]
      exact h1_ih_1 psi a2 M nf hyp V''

      specialize s3 (V' ∘ σ')
      simp only [Function.comp.assoc] at s3
      simp only [a1.right] at s3
      simp only [Function.comp_id] at s3
      exact s3
  case conv h1_Γ h1_Δ h1_phi h1_phi' h1_1 h1_2 h1_3 h1_ih =>
    intro V
    have s1 : Holds D I V M E h1_phi := h1_ih M nf hyp V

    simp only [← holds_conv D I V M E h1_phi h1_phi' h2 h1_3]
    exact s1

end MM0

--#lint
