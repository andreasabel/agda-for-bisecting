-- {-# OPTIONS --without-K #-}
{-# OPTIONS --no-eta-equality #-}

open import Agda.Primitive
  using    (Level; _⊔_; lzero; lsuc)
record CartesianClosedCat {ℓ₀ ℓ₁ ℓ₂} : Set (lsuc (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    Obj   : Set ℓ₀
    _[>]_ : Obj → Obj → Set ℓ₁
    _≈_   : ∀ {a b} → (a [>] b) → (a [>] b) → Set ℓ₂
    id    : ∀ {a} → a [>] a
    _⨾_   : ∀ {a b c} → a [>] b → b [>] c → a [>] c
    𝟙     : Obj
    _×_   : Obj → Obj → Obj
    dup   : ∀ {a} → a [>] (a × a)
    _××_  : ∀ {a b c d} → a [>] c → b [>] d → (a × b) [>] (c × d)
    getl  : ∀ {a b} → (a × b) [>] a
    getr  : ∀ {a b} → (a × b) [>] b
    _~>_   : Obj → Obj → Obj
    curry : ∀ {a b c} → ((a × b) [>] c) → (a [>] (b ~> c))
    apply : ∀ {a b} → (((a ~> b) × a) [>] b)
    *     : ∀ {a} → (a [>] 𝟙)

    _■_      : ∀ {a b} {f g h : a [>] b} → f ≈ g → g ≈ h → f ≈ h
    _⁻¹      : ∀ {a b} {f g : a [>] b} → f ≈ g → g ≈ f
    2id      : ∀ {a b} {f : a [>] b} → f ≈ f
    _⨾-map_ : ∀ {a b c} {f f‵ : a [>] b} {g g‵ : b [>] c} → f ≈ f‵ → g ≈ g‵ → (f ⨾ g) ≈ (f‵ ⨾ g‵)

    lid   : ∀ {a b} {f : a [>] b} → (id ⨾ f) ≈ f
    rid   : ∀ {a b} {f : a [>] b} → (f ⨾ id) ≈ f
    assoc : ∀ {a b c d} {f : a [>] b} {g : b [>] c} {h : c [>] d}
            → ((f ⨾ g) ⨾ h) ≈ (f ⨾ (g ⨾ h))

    *-law : ∀ {a} {f g : a [>] 𝟙} → f ≈ g
    ××id  : ∀ {a b} → (id {a} ×× id {b}) ≈ id
    dup-getl : ∀ {a} → (dup {a} ⨾ getl) ≈ id
    dup-getr : ∀ {a} → (dup {a} ⨾ getr) ≈ id
    ××-natural : ∀ {a b c a′ b′ c′} {f : a [>] b} {g : b [>] c} {f′ : a′ [>] b′} {g′ : b′ [>] c′}
                 → ((f ⨾ g) ×× (f′ ⨾ g′)) ≈ ((f ×× f′) ⨾ (g ×× g′))
    dup-natural : ∀ {a b} {f : a [>] b} → (dup ⨾ (f ×× f)) ≈ (f ⨾ dup)
    getl-natural : ∀ {a b a′ b′} {f : a [>] b} {f′ : a′ [>] b′}
                   → ((f ×× f′) ⨾ getl) ≈ (getl ⨾ f)
    getr-natural : ∀ {a b a′ b′} {f : a [>] b} {f′ : a′ [>] b′}
                   → ((f ×× f′) ⨾ getr) ≈ (getr ⨾ f′)
    _××-2map_ : ∀ {a b a′ b′} {f g : a [>] b} {f′ g′ : a′ [>] b′} → f ≈ g → f′ ≈ g′ → (f ×× f′) ≈ (g ×× g′)

    exp-ρ : ∀ {a b c} {f : (a × b) [>] c}
            → ((curry f ×× id) ⨾ apply) ≈ f
    exp-η : ∀ {a b c} {f : a [>] (b ~> c)}
            → curry ((f ×× id) ⨾ apply) ≈ f

-- some bits of a Presheaf/Family-like object
record Presheaf {ℓ₀ ℓ₁ ℓ₂ ℓp₀ ℓp₁ ℓe₂ ℓp₂} (C : CartesianClosedCat {ℓ₀} {ℓ₁} {ℓ₂}) : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ lsuc (ℓp₀ ⊔ ℓp₁ ⊔ ℓe₂ ⊔ ℓp₂)) where
  open CartesianClosedCat C
  field
    Psh  : Obj → Set ℓp₀
    Π    : ∀ {a} → Psh a → Psh a → Set ℓp₁
  Π_[→]_ : ∀ {a} → Psh a → Psh a → Set ℓp₁
  Π_[→]_ = Π
  Π[_]_[→]_ : ∀ a → Psh a → Psh a → Set ℓp₁
  Π[ a ] x [→] y = Π {a} x y
  field
    _≈ₑ_ : ∀ {a} → Psh a → Psh a → Set ℓp₂ -- equivalence of categories or w/e

    Πid  : ∀ {a x} → Π[ a ] x [→] x
    -- _⨾ₚ_ : ∀ {a} {x y z : Psh a} → Π x [→] y → Π y [→] z → Π x [→] z

    _⨾ₛ_ : ∀ {a b} → (a [>] b) → Psh b → Psh a

    _≈ₚ[_]_ : ∀ {a b x y} {f : a [>] b} {g} → (Π[ a ] x [→] (f ⨾ₛ y)) → f ≈ g → (Π[ a ] x [→] (g ⨾ₛ y)) → Set ℓp₂
    -- _Π⨾ₛ_ : ∀ {a b x y} → (f : a [>] b) → Π[ b ] x [→] y → Π[ a ] (f ⨾ₛ x) [→] (f ⨾ₛ y)
    _⨾ₚ_ : ∀ {a b c x y z} → {f : a [>] b} {g : b [>] c} → Π[ a ] x [→] (f ⨾ₛ y) → Π[ b ] y [→] (g ⨾ₛ z) → Π[ a ] x [→] ((f ⨾ g) ⨾ₛ z)

    --_■ₚ_   : ∀ {a x y} {f g h : Π[ a ] x [→] b} → f ≈ₚ g → g ≈ₚ h → f ≈ₚ h
    --_⁻¹ₚ   : ∀ {a x y} {f g   : Π[ a ] x [→] b} → f ≈ₚ g → g ≈ₚ f
    --2idₚ   : ∀ {a x y} {f     : Π[ a ] x [→] b} → f ≈ₚ f
    --_⨾-mapₚ_

    --lidₚ   : ∀ {a x y} {f : Π[ a ] x [→] y} → (idₚ ⨾ₚ f) ≈ₚ f
    --ridₚ   : ∀ {a x y} {f : Π[ a ] x [→] y} → (f ⨾ₚ idₚ) ≈ₚ f
    --assocₚ : ∀ {a} {x y z w : Psh a} {f : Π x [→] y} {g : Π y [→] z} {h : Π z [→] w}
    --         → (f ⨾ₚ (g ⨾ₚ h)) ≈ₚ ((f ⨾ₚ g) ⨾ₚ h)

    -- TODO: interaction of ≈ₑ and ≈ₚ
    -- TODO: id Π⨾ₛ f = f
    -- TODO: f Π⨾ₛ Πid = Πid
    -- TODO: (f ⨾ g) Π⨾ₛ h = f Π⨾ₛ (g ⨾ₛ h)

    _■ₑ_   : ∀ {a} {x y z : Psh a} → x ≈ₑ y → y ≈ₑ z → x ≈ₑ z
    _⁻¹ₑ   : ∀ {a} {x y : Psh a} → x ≈ₑ y → y ≈ₑ x
    2idₑ   : ∀ {a} {x : Psh a} → x ≈ₑ x

    subst-id  : ∀ {a} {x : Psh a} → (id ⨾ₛ x) ≈ₑ x
    assocₛ    : ∀ {a b c} {f : a [>] b} {g : b [>] c} {x : Psh c} → ((f ⨾ g) ⨾ₛ x) ≈ₑ (f ⨾ₛ (g ⨾ₛ x))
    subst-map : ∀ {a b} {f g : a [>] b} {x : Psh b} → f ≈ g → (f ⨾ₛ x) ≈ₑ (g ⨾ₛ x)

    _Π⨾ₑ_ : ∀ {a} {x y x' y' : Psh a} → x' ≈ₑ x → y ≈ₑ y' → (Π[ a ] x [→] y) → (Π[ a ] x' [→] y')

    --≈ₚ-id : ∀ {a b x y} {f : a [>] b} {g} → (F : Π[ a ] x [→] (f ⨾ₛ y)) → (e : f ≈ g) → (G : Π[ a ] x [→] (g ⨾ₛ y)) → (? ≈


record PresheafHasΣ {ℓ₀ ℓ₁ ℓ₂ ℓp₀ ℓp₁ ℓe₂ ℓp₂} {C : CartesianClosedCat {ℓ₀} {ℓ₁} {ℓ₂}}
                    (T : Presheaf {ℓ₀} {ℓ₁} {ℓ₂} {ℓp₀} {ℓp₁} {ℓe₂} {ℓp₂} C)
                    : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓp₀ ⊔ ℓp₁ ⊔ ℓe₂ ⊔ ℓp₂) where
  open CartesianClosedCat C
  open Presheaf T
  field
    Wk     : Obj → Psh 𝟙 -- weakening over the terminal context
    Wk-map : ∀ {a b} → a [>] b → Π (Wk a) [→] (Wk b)
    -- TODO: id and ⨾ laws targeting ≈ₚ

  𝟙ₚ : ∀ {a} → Psh a
  𝟙ₚ {a} = (* {a}) ⨾ₛ Wk 𝟙
  *ₚ : ∀ {a b} (f : a [>] b) → Π[ a ] 𝟙ₚ [→] (f ⨾ₛ 𝟙ₚ)
  *ₚ f = (2idₑ Π⨾ₑ (subst-map *-law ■ₑ assocₛ)) Πid

  field
    Σ : ∀ {a : Obj} → Psh a → Obj

    dupΣ : ∀ {a} → a [>] Σ {a} 𝟙ₚ
    _ΣΣ_ : ∀ {a b x y} → (f : a [>] b) → (Π[ a ] x [→] (f ⨾ₛ y)) → (Σ {a} x [>] Σ {b} y)
    fst  : ∀ {a x} → Σ {a} x [>] a
    snd  : ∀ {a x} → Π[ Σ {a} x ] 𝟙ₚ [→] (fst ⨾ₛ x)

    -- Σ-map-id : ∀ {a x} → (id ΣΣ Πid) ≈ id {Σ {a} x} -- needs x = (id ⨾ₛ x)
    dup-fst : ∀ {a} → (dupΣ {a} ⨾ fst) ≈ id
    dup-snd : ∀ {a x} → (dupΣ {Σ {a} x} ⨾ (fst ΣΣ snd)) ≈ id
    ΣΣ-natural : ∀ {a b c x y z} {f : a [>] b} {g : b [>] c} {F : Π[ a ] x [→] (f ⨾ₛ y)} {G : Π[ b ] y [→] (g ⨾ₛ z)}
                 → ((f ⨾ g) ΣΣ (F ⨾ₚ G)) ≈ ((f ΣΣ F) ⨾ (g ΣΣ G))
    dup-ΣΣ : ∀ {a b} {f : a [>] b} → (dupΣ ⨾ (f ΣΣ *ₚ f)) ≈ (f ⨾ dupΣ)
    _ΣΣ-2map_ : ∀ {a b x y} {f f′ : a [>] b} {g : Π[ a ] x [→] (f ⨾ₛ y)} {g′ : Π[ a ] x [→] (f′ ⨾ₛ y)}
      → (e : f ≈ f′) → g ≈ₚ[ e ] g′ → (f ΣΣ g) ≈ (f′ ΣΣ g′)

    pair : ∀ {a b y} → (f : a [>] b) → (Π[ a ] 𝟙ₚ [→] (f ⨾ₛ y)) → (a [>] Σ {b} y) -- duplicative
    pair-fst : ∀ {a b y f g} → (pair {a} {b} {y} f g ⨾ fst) ≈ f
    -- pair-snd : ∀ {a b y f g} → (pair {a} {b} {y} f g ⨾ₛ snd) ≈ₚ g
    pair-η   : ∀ {a b y} {f : a [>] Σ {b} y} → (pair (f ⨾ fst) (*ₚ f ⨾ₚ snd)) ≈ f
    pair-2map : ∀ {a b y f f' g g'} → (e : f ≈ f') → g ≈ₚ[ e ] g' → pair {a} {b} {y} f g ≈ pair {a} {b} {y} f' g'

    -- should be derivable...
    pair-dup : ∀ {a b y f g} → pair {a} {b} {y} f g ≈ (dupΣ ⨾ (f ΣΣ g))
    -- pair-dup = pair-2map ({!? ■ (2id ⨾-map  !} ■ (assoc ⁻¹)) {!!} ■ pair-η


    pair-wk : ∀ {a x} → Π[ a ] x [→] (* ⨾ₛ Wk (Σ {a} x))
    𝟙-law   : ∀ {a} → Σ (Wk a) [>] a
    -- TODO: more rules about Σ
    -- ρ₁ : (Σ.μ * ι); ε = id
    -- ρ₂ : ι; (μ ε)[*] = id
    -- μ-natural : μ (p; q) = μ p; μ q
    -- ι-natural : ι; μ (Σ.μ f g) = g; ι[f]
    -- ε-natural : (Σ.μ * (μ p)); ε = ε; p
    -- alt: uncurryΣ : ∀ {a b x} → (Σ {a} x [>] b) → (Π[ a ] x [→] (* ⨾ₛ Wk b))
    uncurryΣ : ∀ {a b x} → (Σ {a} x [>] b) → (Π[ a ] x [→] (* ⨾ₛ Wk b))

-- a semicomonad that codistributes over 𝟙 and _×_ (since behavior of
-- _~>_ is determined by _×_, we do not need any laws about
-- interaction with _~>_) and Σ
record CodistributiveSemicomonad {ℓ₀ ℓ₁ ℓ₂ ℓp₀ ℓp₁ ℓe₂ ℓp₂} (C : CartesianClosedCat {ℓ₀} {ℓ₁} {ℓ₂})
                                 (T : Presheaf {ℓ₀} {ℓ₁} {ℓ₂} {ℓp₀} {ℓp₁} {ℓe₂} {ℓp₂} C)
                                 (TΣ : PresheafHasΣ T)
                                 : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓp₀ ⊔ ℓp₁ ⊔ ℓe₂ ⊔ ℓp₂) where
  open CartesianClosedCat C
  field
    □     : Obj → Obj
    □-map : ∀ {a b} → a [>] b → □ a [>] □ b

    cojoin : ∀ {a} → □ a [>] □ (□ a)

    □-𝟙-codistr  : 𝟙 [>] □ 𝟙
    □-×-codistr  : ∀ {a b} → (□ a × □ b) [>] □ (a × b)

    □-id    : ∀ {a} → □-map (id {a}) ≈ id
    □-⨾-map : ∀ {a b c} {f : a [>] b} {g : b [>] c} → □-map (f ⨾ g) ≈ (□-map f ⨾ □-map g)

    □-2map  : ∀ {a b} {f f′ : a [>] b} → (f ≈ f′) → (□-map f) ≈ (□-map f′)

    -- points are quoted with `□-𝟙-codistr ⨾ □-map`, quoted terms are
    -- requoted with `cojoin`; these must agree on closed quoted terms
    □-map-cojoin : ∀ {a} {f : 𝟙 [>] □ a} → (f ⨾ cojoin) ≈ (□-𝟙-codistr ⨾ □-map f)

    □-×-codistr-dup  : ∀ {a} → (dup {□ a} ⨾ □-×-codistr) ≈ □-map dup
    □-map-××-codistr : ∀ {a b c d} {f : a [>] b} {g : c [>] d}
                       → ((□-map f ×× □-map g) ⨾ □-×-codistr) ≈ (□-×-codistr ⨾ □-map (f ×× g))

  open Presheaf T
  open PresheafHasΣ TΣ
  field
    □ₚ : ∀ {a} → Psh a → Psh (□ a)
    □ₚ-map : ∀ {a b x y} → {f : a [>] b} → (Π[ a ] x [→] (f ⨾ₛ y)) → (Π[ □ a ] (□ₚ x) [→] (□-map f ⨾ₛ □ₚ y))

    -- TODO: other fields

    □ₚ-𝟙-codistr  : Π 𝟙ₚ [→] (□-𝟙-codistr ⨾ₛ □ₚ 𝟙ₚ)
    -- □ₚ-𝟙-codistr'  : Π[ □ 𝟙 ] 𝟙ₚ [→] (id ⨾ₛ □ₚ 𝟙ₚ) -- ???
    □-Wk-codistr : ∀ {a} → Π[ 𝟙 ] (Wk (□ a)) [→] (□-𝟙-codistr ⨾ₛ □ₚ (Wk a))
    □-Σ-codistr : ∀ {a x} → (Σ {□ a} (□ₚ x)) [>] (□ (Σ {a} x))

    □-map-subst : ∀ {a b x} {f : a [>] b} → (□-map f ⨾ₛ □ₚ x) ≈ₑ □ₚ (f ⨾ₛ x)

    □-map-ΣΣ-codistr : ∀ {a b x y} {f : a [>] b} {g : Π[ a ] x [→] (f ⨾ₛ y)} → ((□-map f ΣΣ □ₚ-map g) ⨾ □-Σ-codistr) ≈ (□-Σ-codistr ⨾ □-map (f ΣΣ g))
    -- dupΣ-□-𝟙-ΣΣ-codistr : (dupΣ {𝟙} ⨾ (□-𝟙-codistr ΣΣ □ₚ-𝟙-codistr)) ≈ (□-𝟙-codistr ⨾ (? ⨾ {!□-Σ-codistr!}))
