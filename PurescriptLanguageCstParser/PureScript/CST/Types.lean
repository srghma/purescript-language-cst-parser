import NonEmpty.CorrectByConstruction.Array
import NonEmpty.String
import Aesop

open NonEmpty.CorrectByConstruction.Array
open NonEmpty.String

namespace PureScript.CST.Types

def ModuleName := NonEmptyString
  deriving Repr, BEq, Ord

structure SourcePos where
  line : USize
  column : USize
  deriving Repr, BEq, Ord, Inhabited

structure SourceRange where
  start : SourcePos
  end_ : SourcePos
  deriving Repr, BEq, Ord, Inhabited

inductive CommentWithoutLine
  | Comment (s : NonEmptyString)
  | Space (i : USize)
  deriving Repr, BEq, Ord

inductive Comment (l : Type)
  | Comment (s : NonEmptyString)
  | Space (i : USize)
  | Line (l : l) (i : USize)
  deriving Repr, BEq, Ord

inductive LineFeed
  | LF
  | CRLF
  deriving Repr, BEq, Ord

inductive SourceStyle
  | ASCII
  | Unicode
  deriving Repr, BEq, Ord

inductive IntValue
  | SmallInt (i : USize)
  | BigInt (s : NonEmptyString)
  | BigHex (s : NonEmptyString)
  deriving Repr, BEq, Ord

inductive Token
  | LeftParen
  | RightParen
  | LeftBrace
  | RightBrace
  | LeftSquare
  | RightSquare
  | LeftArrow (style : SourceStyle)
  | RightArrow (style : SourceStyle)
  | RightFatArrow (style : SourceStyle)
  | DoubleColon (style : SourceStyle)
  | Forall (style : SourceStyle)
  | Equals
  | Pipe
  | Tick
  | Dot
  | Comma
  | Underscore
  | Backslash
  | At
  | LowerName (module_ : Option ModuleName) (name : NonEmptyString)
  | UpperName (module_ : Option ModuleName) (name : NonEmptyString)
  | Operator (module_ : Option ModuleName) (name : NonEmptyString)
  | SymbolName (module_ : Option ModuleName) (name : NonEmptyString)
  | SymbolArrow (style : SourceStyle)
  | Hole (name : NonEmptyString)
  | Char (s : NonEmptyString) (c : Char)
  | NonEmptyString (s : NonEmptyString) (value : NonEmptyString)
  | RawString (s : NonEmptyString)
  | Int (s : NonEmptyString) (value : IntValue)
  | Number (s : NonEmptyString) (value : Float)
  | LayoutStart (i : USize)
  | LayoutSep (i : USize)
  | LayoutEnd (i : USize)
  deriving Repr, BEq --, Ord -- bc of Float

structure SourceToken where
  range : SourceRange
  leadingComments : Array (Comment LineFeed)
  trailingComments : Array CommentWithoutLine
  value : Token
  deriving Repr, BEq

def Ident := NonEmptyString
  deriving Repr, BEq, Ord

def Proper := NonEmptyString
  deriving Repr, BEq, Ord

def Label := NonEmptyString
  deriving Repr, BEq, Ord

def Operator := NonEmptyString
  deriving Repr, BEq, Ord

structure Name (α : Type) where
  token : SourceToken
  name : α
  deriving Repr, BEq

@[always_inline] instance : Functor Name where map f n := { n with name := f n.name }

instance : LawfulFunctor Name where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

@[simp] theorem Name.id_map {α : Type} (n : Name α) : (id <$> n) = n := rfl
@[simp] theorem Name.comp_map {α β γ : Type} (g : α → β) (h : β → γ) (n : Name α) : (h <$> g <$> n) = ((h ∘ g) <$> n) := rfl

structure QualifiedName (α : Type) where
  token : SourceToken
  module_ : Option ModuleName
  name : α
  deriving Repr, BEq

@[always_inline] instance : Functor QualifiedName where map f n := { n with name := f n.name }

instance : LawfulFunctor QualifiedName where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

@[simp] theorem QualifiedName.id_map {α : Type} (n : QualifiedName α) : (id <$> n) = n := rfl
@[simp] theorem QualifiedName.comp_map {α β γ : Type} (g : α → β) (h : β → γ) (n : QualifiedName α) : (h <$> g <$> n) = ((h ∘ g) <$> n) := rfl

structure Wrapped (α : Type) where
  open_ : SourceToken
  value : α
  close : SourceToken
  deriving Repr, BEq

@[always_inline] instance : Functor Wrapped where
  map f w := { w with value := f w.value }

instance : LawfulFunctor Wrapped where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

@[simp] theorem Wrapped.id_map {α : Type} (w : Wrapped α) : (id <$> w) = w := rfl
@[simp] theorem Wrapped.comp_map {α β γ : Type} (g : α → β) (h : β → γ) (w : Wrapped α) : (h <$> g <$> w) = ((h ∘ g) <$> w) := rfl

structure Separated (α : Type) where
  head : α
  tail : Array (SourceToken × α)
  deriving Repr, BEq

namespace Separated

@[always_inline, simp] def map {α β : Type} (g : α → β) (s : Separated α) : Separated β := { head := g s.head, tail := s.tail.map (fun (tok, a) => (tok, g a)) }

@[simp] theorem id_map {α : Type} (s : Separated α) : (s.map id) = s := by
  simp_all only [map, id_eq, Array.map_id_fun']

@[simp] theorem comp_map {α β γ : Type} (g : α → β) (h : β → γ) (s : Separated α) : (s.map (h ∘ g)) = (s.map g |>.map h) := by
  funext
  simp_all only [map, Function.comp, Array.map_map, Separated.mk.injEq, Array.map_inj_left,
      implies_true, and_self]

@[simp] theorem map_id_fun {α : Type} : map (id : α → α) = id := by funext s; exact id_map s

@[simp] theorem map_comp_fun {α β γ : Type} (g : α → β) (h : β → γ) : map (h ∘ g) = map h ∘ map g := by funext s; exact comp_map g h s

end Separated

@[always_inline] instance : Functor Separated where
  map := Separated.map

instance : LawfulFunctor Separated where
  map_const := rfl
  id_map s := Separated.id_map s
  comp_map g h s := Separated.comp_map g h s

structure Labeled (α β : Type) where
  label : α
  separator : SourceToken
  value : β
  deriving Repr, BEq

namespace Labeled

@[always_inline] def map_label {α β x : Type} (g : α → β) (l : Labeled α x) : Labeled β x := { l with label := g l.label }

@[always_inline] def map_value {α β γ : Type} (g : β → γ) (l : Labeled α β) : Labeled α γ := { l with value := g l.value }

@[simp] theorem map_value_id {α β : Type} (l : Labeled α β) : map_value (id : β → β) l = l := rfl
@[simp] theorem map_value_comp {α β γ δ : Type} (g : β → γ) (h : γ → δ) (l : Labeled α β) : map_value (h ∘ g) l = map_value h (map_value g l) := rfl

@[simp] theorem map_label_id {α β : Type} (l : Labeled α β) : map_label (id : α → α) l = l := rfl
@[simp] theorem map_label_comp {α β γ δ : Type} (g : α → β) (h : β → γ) (l : Labeled α δ) : map_label (h ∘ g) l = map_label h (map_label g l) := rfl

@[simp] theorem map_label_id_fun {α β : Type} : map_label (id : α → α) = (id : Labeled α β → Labeled α β) := by funext l; exact map_label_id l
@[simp] theorem map_value_id_fun {α β : Type} : map_value (id : β → β) = (id : Labeled α β → Labeled α β) := by funext l; exact map_value_id l

@[simp] theorem map_label_comp_fun {α β γ δ : Type} (g : α → β) (h : β → γ) :
  map_label (h ∘ g) = (map_label h ∘ map_label g : Labeled α δ → Labeled γ δ) := by funext l; exact map_label_comp g h l
@[simp] theorem map_value_comp_fun {α β γ δ : Type} (g : β → γ) (h : γ → δ) :
  map_value (h ∘ g) = (map_value h ∘ map_value g : Labeled α β → Labeled α δ) := by funext l; exact map_value_comp g h l

end Labeled

@[always_inline] instance : Functor (Labeled α) where
  map := Labeled.map_value

instance : LawfulFunctor (Labeled α) where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

structure Prefixed (α : Type) where
  prefix_ : Option SourceToken
  value : α
  deriving Repr, BEq

namespace Prefixed

@[always_inline] def map (f : α → β) (p : Prefixed α) : Prefixed β := { p with value := f p.value }

@[simp] theorem id_map {α : Type} (p : Prefixed α) : (map id p) = p := rfl
@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (p : Prefixed α) : (map (g ∘ f) p) = (map g (map f p)) := rfl

end Prefixed

@[always_inline] instance : Functor Prefixed where map := Prefixed.map
instance : LawfulFunctor Prefixed where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

-- why not def or abbrev? will break in recursive inductive types (e.g. Expr)
inductive Delimited (α : Type)
  | mk (v : Wrapped (Option (Separated α)))
  deriving Repr, BEq

namespace Delimited

@[always_inline, simp] def map (f : α → β) : Delimited α → Delimited β
  | .mk v => .mk { v with value := (Separated.map f) <$> v.value }

@[simp] theorem id_map {α : Type} (d : Delimited α) : map id d = d := by
  cases d with | mk v =>
  simp [map, Separated.map_id_fun]

@[simp] theorem comp_map {α β γ : Type} (f : α → β) (g : β → γ) (d : Delimited α) : (map (g ∘ f) d) = (map g (map f d)) := by
  cases d with | mk v =>
  simp [map, Separated.map_comp_fun]

end Delimited

@[always_inline] instance : Functor Delimited where
  map := Delimited.map

instance : LawfulFunctor Delimited where
  map_const := rfl
  id_map := Delimited.id_map
  comp_map := Delimited.comp_map

inductive DelimitedNonEmpty (α : Type)
  | mk (v : Wrapped (Separated α))
  deriving Repr, BEq

instance : Functor DelimitedNonEmpty where
  map f | .mk w => .mk { w with value := ( (f <$> w.value)) }

instance : LawfulFunctor DelimitedNonEmpty where
  map_const := rfl
  id_map | .mk w => by simp [Functor.map]
  comp_map g h | .mk w => by simp [Functor.map]

inductive OneOrDelimited (α : Type)
  | One (value : α)
  | Many (separated : DelimitedNonEmpty α)
  deriving Repr, BEq

instance : Functor OneOrDelimited where
  map f
    | .One a  => .One (f a)
    | .Many m => .Many (f <$> m)

instance : LawfulFunctor OneOrDelimited where
  map_const := rfl
  id_map a := by cases a <;> simp [Functor.map]
  comp_map g h a := by cases a <;> simp [Functor.map]

-- Note: the above requires Functor for DelimitedNonEmpty, defined below.

structure TokenAnd (α : Type) where
  token : SourceToken
  value : α
  deriving Repr, BEq

@[always_inline] instance : Functor TokenAnd where map f t := { t with value := f t.value }

instance : LawfulFunctor TokenAnd where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

inductive TypeVarBindingF (name type_e : Type)
  | Kinded (wrapped : Wrapped (Labeled name type_e))
  | Name (name : name)
  deriving Repr, BEq

instance : Functor (TypeVarBindingF name_e) where
  map f
    | .Kinded w => .Kinded ((f <$> ·) <$> w)  -- Wrapped (Labeled a type_e)
    | .Name n   => .Name n

instance : LawfulFunctor (TypeVarBindingF a) where
  map_const := rfl
  id_map t  := by cases t <;> rfl
  comp_map g h t := by cases t <;> rfl

namespace TypeVarBindingF

@[simp] theorem id_map {a α : Type} (t : TypeVarBindingF a α) : (id <$> t) = t := LawfulFunctor.id_map t
@[simp] theorem comp_map {a α β γ : Type} (g : α → β) (h : β → γ) (t : TypeVarBindingF a α) : (h <$> g <$> t) = ((h ∘ g) <$> t) := (LawfulFunctor.comp_map g h t).symm

def map_name {a b α : Type} (g : a → b) : TypeVarBindingF a α → TypeVarBindingF b α
  | .Kinded w => .Kinded (Labeled.map_label g <$> w)
  | .Name n   => .Name (g n)

@[simp] theorem map_name_id {a α : Type} (t : TypeVarBindingF a α) : map_name (id : a → a) t = t := by
  cases t <;> simp only [map_name, Labeled.map_label_id_fun, LawfulFunctor.id_map, id_eq]

@[simp] theorem map_name_comp {a b c α : Type} (ga : a → b) (gb : b → c) (t : TypeVarBindingF a α) :
  map_name (gb ∘ ga) t = map_name gb (map_name ga t) := by
  cases t <;> simp only [map_name, Labeled.map_label_comp_fun, LawfulFunctor.comp_map,
    Functor.map_map, Function.comp_apply]

end TypeVarBindingF

structure RowF (e type_e : Type) where
  labels : Option (Separated (Labeled (Name Label) (type_e)))
  tail : Option (SourceToken × type_e)
  deriving Repr, BEq

namespace RowF
@[simp] def map (f : type_e → type_e') : RowF e type_e → RowF e type_e'
  | { labels, tail } => {
    labels := labels.map (Separated.map (Labeled.map_value f))
    tail   := tail.map (fun (tok, t) => (tok, f t))
  }

@[simp] theorem id_map {e α : Type} (r : RowF e α) : (map id r) = r := by
  cases r; simp [map, Separated.map_id_fun, Labeled.map_value_id_fun]

@[simp] theorem comp_map {e α β γ : Type} (f : α → β) (g : β → γ) (r : RowF e α) : (map (g ∘ f) r) = (map g (map f r)) := by
  cases r with | mk l t =>
  simp [map, Separated.map_comp_fun, Labeled.map_value_comp_fun, Option.map_map]
  cases t <;> rfl

end RowF

instance : Functor (RowF e) where
  map := RowF.map

instance : LawfulFunctor (RowF e) where
  map_const := rfl
  id_map r := RowF.id_map r
  comp_map g h r := RowF.comp_map g h r

namespace RowF
  def map_e {e f α : Type} (_g : e → f) (r : RowF e α) : RowF f α :=
    { labels := r.labels, tail := r.tail }

  @[simp] theorem map_e_id {e α : Type} (r : RowF e α) : map_e (id : e → e) r = r := by
    cases r
    simp only [map_e]

  @[simp] theorem map_e_comp {e f g α : Type} (ge : e → f) (gf : f → g) (r : RowF e α) :
    map_e (gf ∘ ge) r = map_e gf (map_e ge r) := by
    cases r
    simp only [map_e]

  @[simp] theorem map_comm {e f α β : Type} (ge : e → f) (ga : α → β) (r : RowF e α) :
    ga <$> (map_e ge r) = map_e ge (ga <$> r) := rfl

end RowF

inductive TypeF (e type_e : Type)
  | Var (name : Name Ident)
  | Constructor (name : QualifiedName Proper)
  | Wildcard (token : SourceToken)
  | Hole (name : Name Ident)
  | NonEmptyString (token : SourceToken) (value : NonEmptyString)
  | Int (prefix_ : Option SourceToken) (token : SourceToken) (value : IntValue)
  | Row (wrapped : Wrapped (RowF e type_e))
  | Record (wrapped : Wrapped (RowF e type_e))
  | Forall (open_ : SourceToken) (bindings : NonEmptyArray (TypeVarBindingF (Prefixed (Name Ident)) type_e)) (close : SourceToken) (body : type_e)
  | Kinded (type_ : type_e) (sep : SourceToken) (kind : type_e)
  | App (fn : type_e) (args : NonEmptyArray type_e)
  | Op (first : type_e) (ops : NonEmptyArray (QualifiedName Operator × type_e))
  | OpName (name : QualifiedName Operator)
  | Arrow (dom : type_e) (token : SourceToken) (codom : type_e)
  | ArrowName (token : SourceToken)
  | Constrained (type_ : type_e) (token : SourceToken) (body : type_e)
  | Parens (wrapped : Wrapped type_e)
  | Error (data : e)
  deriving Repr, BEq

namespace TypeF

  @[simp] def map (f : type_a -> type_b) : TypeF e type_a → TypeF e type_b
    | .Var n                    => .Var n
    | .Constructor n            => .Constructor n
    | .Wildcard t               => .Wildcard t
    | .Hole n                   => .Hole n
    | .NonEmptyString t v       => .NonEmptyString t v
    | .Int p t v                => .Int p t v
    | .Row w                    => .Row ((f <$> ·) <$> w)   -- Wrapped (RowF e type_e)
    | .Record w                 => .Record ((f <$> ·) <$> w)
    | .Forall o bs c body       => .Forall o (bs.map (f <$> ·)) c (f body)
    | .Kinded t sep k           => .Kinded (f t) sep (f k)
    | .App fn args              => .App (f fn) (args.map f)
    | .Op first ops             => .Op (f first) (ops.map fun (op, t) => (op, f t))
    | .OpName n                 => .OpName n
    | .Arrow dom tok codom      => .Arrow (f dom) tok (f codom)
    | .ArrowName t              => .ArrowName t
    | .Constrained t tok body   => .Constrained (f t) tok (f body)
    | .Parens w                 => .Parens (f <$> w)  -- Wrapped type_e
    | .Error e                  => .Error e            -- e ≠ type_e, unchanged

  @[simp] theorem map_id {e α : Type} (t : TypeF e α) : map (id : α → α) t = t := by
    cases t <;> simp only [map, id_map, id_map', id_eq, NonEmptyArray.map, id_map, Array.map_id_fun', Array.map_id_fun]

  @[simp] theorem map_comp {e α β γ : Type} (g : α → β) (h : β → γ) (t : TypeF e α) :
    map (h ∘ g) t = map h (map g t) := by
    cases t
    · simp_all only [map]
    · simp_all only [map]
    · simp_all only [map]
    · simp_all only [map]
    · simp_all only [map]
    · simp_all only [map]
    · simp_all only [map, Functor.map_map, Row.injEq]
      rfl
    · simp_all only [map, Functor.map_map, Record.injEq]
      rfl
    · simp_all only [map, NonEmptyArray.map, Function.comp_apply, Functor.map_map, Array.map_map, Forall.injEq, NonEmptyArray.mk.injEq, Array.map_inj_left, and_self, and_true, true_and]
      apply And.intro
      · rfl
      · intro a a_1
        rfl
    · simp_all only [map, Function.comp_apply]
    · simp_all only [map, Function.comp_apply, NonEmptyArray.map, Array.map_map]
    · simp_all only [map, Function.comp_apply, NonEmptyArray.map, Array.map_map, Op.injEq, NonEmptyArray.mk.injEq,
      Array.map_inj_left, implies_true, and_self]
    · simp_all only [map]
    · simp_all only [map, Function.comp_apply]
    · simp_all only [map]
    · simp_all only [map, Function.comp_apply]
    · simp_all only [map, Functor.map_map, Parens.injEq]
      rfl
    · simp_all only [map]

  @[simp] def map_e {e f α : Type} (g : e → f) : TypeF e α → TypeF f α
    | .Row w => .Row { w with value := RowF.map_e g w.value }
    | .Record w => .Record { w with value := RowF.map_e g w.value }
    | .Error e_val => .Error (g e_val)
    -- All other cases don't contain 'e', so they are identities
    | .Var n => .Var n
    | .Constructor n => .Constructor n
    | .Wildcard t => .Wildcard t
    | .Hole n => .Hole n
    | .NonEmptyString t v => .NonEmptyString t v
    | .Int p t v => .Int p t v
    | .Forall o bs c body => .Forall o bs c body
    | .Kinded t sep k => .Kinded t sep k
    | .App fn args => .App fn args
    | .Op first ops => .Op first ops
    | .OpName n => .OpName n
    | .Arrow dom tok codom => .Arrow dom tok codom
    | .ArrowName t => .ArrowName t
    | .Constrained t tok body => .Constrained t tok body
    | .Parens w => .Parens w

  @[simp] theorem map_e_id {e α : Type} (t : TypeF e α) : map_e (id : e → e) t = t := by
    cases t <;> simp only [map_e, id_eq, RowF.map_e_id]

  @[simp] theorem map_e_comp {e f g α : Type} (ge : e → f) (gf : f → g) (t : TypeF e α) :
    map_e (gf ∘ ge) t = map_e gf (map_e ge t) := by
    cases t <;> simp only [map_e, RowF.map_e_comp, Function.comp_apply]

  @[simp] theorem map_map_e_comm {e f α β : Type} (gf : e → f) (ga : α → β) (t : TypeF e α) :
    map ga (map_e gf t) = map_e gf (map ga t) := by
    cases t <;> rfl

  @[simp] def map_bi {e f α β : Type} (ge : e → f) (ga : α → β) (t : TypeF e α) : TypeF f β :=
    map ga (map_e ge t)

  @[simp] theorem map_bi_id_id {e α : Type} (t : TypeF e α) : map_bi (id : e → e) (id : α → α) t = t := by
    simp_all only [map_bi]
    cases t <;> simp only [map, map_e, NonEmptyArray.map, id_map, Array.map_id_fun, Array.map_id_fun', id_eq, RowF.map_e_id, id_map, id_map']

  @[simp] theorem map_bi_comp {e f g α β γ : Type} (ge : e → f) (gf : f → g) (ga : α → β) (gb : β → γ) (t : TypeF e α) :
    map_bi (gf ∘ ge) (gb ∘ ga) t = map_bi gf gb (map_bi ge ga t) := by
    simp only [map_bi, map_comp, map_e_comp, map_map_e_comm]
end TypeF

instance : Functor (TypeF e) where
  map := TypeF.map

instance : LawfulFunctor (TypeF e) where
  map_const := rfl
  id_map t := by simp only [Functor.map, TypeF.map_id]
  comp_map g h t := by simp only [Functor.map, TypeF.map_comp]

inductive Type_ (e : Type)
  | mk (value : TypeF e (Type_ e))
  deriving Repr, BEq

-- def Type_.map {e f : Type} (g : e → f) : Type_ e → Type_ f
--   | .mk v => .mk (TypeF.map_bi g (Type_.map g) v)
-- termination_by t => sizeOf t


mutual
  def Type_.map {e f : Type} (g : e → f) : Type_ e → Type_ f
    | .mk v => .mk (TypeF.mapGo g v)

  -- TypeF pattern match exposes direct subterms:
  def TypeF.mapGo {e f : Type} (g : e → f)
      : TypeF e (Type_ e) → TypeF f (Type_ f)
    | .Var n                   => .Var n
    | .Constructor n           => .Constructor n
    | .Wildcard t              => .Wildcard t
    | .Hole n                  => .Hole n
    | .NonEmptyString t v      => .NonEmptyString t v
    | .Int p t v               => .Int p t v
    | .Kinded t sep k          => .Kinded (Type_.map g t) sep (Type_.map g k)  -- ✓ subterms
    | .Arrow d tok c           => .Arrow (Type_.map g d) tok (Type_.map g c)    -- ✓ subterms
    | .Constrained t tok b     => .Constrained (Type_.map g t) tok (Type_.map g b) -- ✓
    | .Parens w                => .Parens { w with value := Type_.map g w.value }  -- ✓ w.value is subterm
    | .Error e                 => .Error (g e)
    | .OpName n                => .OpName n
    | .ArrowName t             => .ArrowName t
    -- Array cases: still need the size lemma or workaround:
    | .App fn args             =>
        .App (Type_.map g fn)
             (args.mapIdx (fun i x =>
               have : sizeOf x < sizeOf (PureScript.CST.Types.TypeF.App fn args) := by
                 simp [SizeOf.sizeOf, TypeF.instSizeOf]
                 exact Nat.lt_of_lt_of_le
                   (NonEmptyArray.sizeOf_get_lt args i)
                   (by omega)
               Type_.map g x))
    | .Forall o bs c body      =>
        .Forall o (bs.mapIdx (fun i x =>
                    have : sizeOf x.value < sizeOf (PureScript.CST.Types.TypeF.Forall o bs c body) := by
                      sorry -- NonEmptyArray.sizeOf_get_lt + Labeled.sizeOf_value_lt
                    Type_.map g <$> x))
                  c (Type_.map g body)
    | .Op first ops            =>
        .Op (Type_.map g first)
            (ops.mapIdx (fun i ⟨op, t⟩ =>
              have : sizeOf t < sizeOf (PureScript.CST.Types.TypeF.Op first ops) := by sorry
              (op, Type_.map g t)))
    | .Row w  => .Row  (RowF.mapGo g <$> w)
    | .Record w => .Record (RowF.mapGo g <$> w)

  def RowF.mapGo {e f : Type} (g : e → f)
      : RowF e (Type_ e) → RowF f (Type_ f)
    | r => {
        labels := r.labels.map (fun sep => sep.map (fun l =>
          { l with value := Type_.map g l.value }))
        tail := r.tail.map (fun (tok, t) => (tok, Type_.map g t))
      }
end
termination_by
  Type_.map _ t => sizeOf t
  TypeF.mapGo _ v => sizeOf v
  RowF.mapGo _ r => sizeOf r


-- instance : Functor Type_ where map := Type_.map

-- instance : LawfulFunctor Type_ where
--   map_const := rfl
--   id_map t := by
--     induction t with | mk v ih =>
--       simp only [Functor.map, Type_.map]
--       have : TypeF.map_bi id (Type_.map id) v = v := by
--         simp only [TypeF.map_bi, TypeF.map_e_id]
--         rw [← TypeF.map_id v]
--         congr; funext x; exact ih x
--       exact congr_arg Type_.mk this
--   comp_map g h t := by
--     induction t with | mk v ih =>
--       simp only [Functor.map, Type_.map]
--       have : TypeF.map_bi (h ∘ g) (Type_.map (h ∘ g)) v =
--              TypeF.map_bi h (Type_.map h) (TypeF.map_bi g (Type_.map g) v) := by
--         rw [TypeF.map_bi_comp]
--         congr; funext x; exact ih x
--       exact congr_arg Type_.mk this

---------------------------------------------------------------------------------------------------------
inductive DataMembers
  | All (token : SourceToken)
  | Enumerated (separated : Delimited (Name Proper))
  deriving Repr, BEq

inductive Export (e : Type)
  | Value (name : Name Ident)
  | Op (name : Name Operator)
  | Type_ (name : Name Proper) (optionMembers : Option DataMembers)
  | TypeOp (token : SourceToken) (name : Name Operator)
  | Class (token : SourceToken) (name : Name Proper)
  | Module (token : SourceToken) (name : Name ModuleName)
  | Error (data : e)
  deriving Repr, BEq

---------------------------------------------------------------------------------------------------------
structure DataHead (e : Type) where
  keyword : SourceToken
  name : Name Proper
  parameters : Array (TypeVarBindingF (Name Ident) (Type_ e))
  deriving Repr, BEq

structure DataCtor (e : Type) where
  name : Name Proper
  parameters : Array (Type_ e)
  deriving Repr, BEq

inductive ClassFundep
  | Determined (token : SourceToken) (names : NonEmptyArray (Name Ident))
  | Determines (left : NonEmptyArray (Name Ident)) (token : SourceToken) (right : NonEmptyArray (Name Ident))
  deriving Repr, BEq

structure ClassHead (e : Type) where
  keyword : SourceToken
  typeConstraint : Option (OneOrDelimited (Type_ e) × SourceToken)
  name : Name Proper
  parameters : Array (TypeVarBindingF (Name Ident) (Type_ e))
  fundependencies : Option (SourceToken × Separated ClassFundep)
  deriving Repr, BEq

structure InstanceHead (e : Type) where
  keyword : SourceToken
  name : Option (Name Ident × SourceToken)
  constraints : Option (OneOrDelimited (Type_ e) × SourceToken)
  className : QualifiedName Proper
  types : Array (Type_ e)
  deriving Repr, BEq

inductive RecordLabeled (a : Type)
  | Pun (name : Name Ident)
  | Field (label : Name Label) (separator : SourceToken) (value : a)
  deriving Repr, BEq

@[always_inline] instance : Functor RecordLabeled where
  map f
    | .Pun n         => .Pun n
    | .Field l sep v => .Field l sep (f v)

instance : LawfulFunctor RecordLabeled where
  map_const := rfl
  id_map a := by cases a <;> rfl
  comp_map _ _ a := by cases a <;> rfl

inductive BinderF (e binder_e : Type)
  | Wildcard (token : SourceToken)
  | Var (name : Name Ident)
  | Named (name : Name Ident) (token : SourceToken) (binder : binder_e)
  | Constructor (name : QualifiedName Proper) (args : Array binder_e)
  | Boolean (token : SourceToken) (val : Bool)
  | Char (token : SourceToken) (val : Char)
  | NonEmptyString (token : SourceToken) (val : NonEmptyString)
  | Int (prefix_ : Option SourceToken) (token : SourceToken) (val : IntValue)
  | Number (prefix_ : Option SourceToken) (token : SourceToken) (val : Float)
  | Array (items : Delimited (binder_e))
  | Record (fields : Delimited (RecordLabeled (binder_e)))
  | Parens (wrapped : Wrapped (binder_e))
  | Typed (binder : binder_e) (token : SourceToken) (type_ : Type_ e)
  | Op (first : binder_e) (ops : NonEmptyArray (QualifiedName Operator × binder_e))
  | Error (data : e)
  deriving Repr, BEq

inductive Binder (e : Type)
  | mk : BinderF e (Binder e) → Binder e
  deriving Repr, BEq

structure AndToken (α : Type) where
  value : α
  token : SourceToken
  deriving Repr, BEq

inductive AppSpineF (e expr_e : Type)
  | Type_ (token : SourceToken) (type_ : Type_ e)
  | Term (expr : expr_e)
  deriving Repr, BEq

inductive RecordUpdateF (e expr_e : Type)
  | Leaf (label : Name Label) (token : SourceToken) (expr : expr_e)
  | Branch (label : Name Label) (updates : DelimitedNonEmpty (RecordUpdateF e expr_e))
  deriving Repr, BEq

structure RecordAccessorF (expr_e : Type) where
  expr : expr_e
  dot : SourceToken
  path : Separated (Name Label)
  deriving Repr, BEq

structure LambdaF (e expr_e : Type) where
  symbol : SourceToken
  binders : NonEmptyArray (Binder e)
  arrow : SourceToken
  body : expr_e
  deriving Repr, BEq

structure IfThenElseF (expr_e : Type) where
  keyword : SourceToken
  cond : expr_e
  then_ : SourceToken
  true_ : expr_e
  else_ : SourceToken
  false_ : expr_e
  deriving Repr, BEq

structure PatternGuardF (e expr_e : Type) where
  binder : Option (Binder e × SourceToken)
  expr : expr_e
  deriving Repr, BEq

-- ```mermaid
-- graph TD
--     LB[LetBindingF] -->|Pattern| W[WhereF]
--     LB -->|Name| VBF[ValueBindingFieldsF]
--
--     VBF -->|guarded| G[GuardedF]
--
--     G -->|Unconditional| W
--     G -->|Guarded| GE[GuardedExprF]
--
--     GE -->|where_| W
--
--     W -->|bindings| LB
--
--     subgraph "The Mutual Cycle"
--     LB
--     VBF
--     G
--     GE
--     W
--     end
-- ```

-- 1. GuardExpr depends only on Where
structure GuardedExprF (e expr_e where_e : Type) where
  bar        : SourceToken
  patterns   : Separated (PatternGuardF e expr_e)
  separator  : SourceToken
  where_     : where_e
  deriving Repr, BEq

-- 2. Guarded depends on Where and GuardExpr
inductive GuardedF (e expr_e where_e guardedExpr_e : Type) where
  | Unconditional (token : SourceToken) (where_ : where_e)
  | Guarded (branches : NonEmptyArray guardedExpr_e)
  deriving Repr, BEq

-- 3. ValueBindingFields depends on Guarded
structure ValueBindingFieldsF (e expr_e guardedExpr_e : Type) where
  name    : Name Ident
  binders : Array (Binder e)
  guarded : guardedExpr_e
  deriving Repr, BEq
-- 4. Where depends on the list of Bindings
structure WhereF (e expr_e letBinding_e : Type) where
  expr     : expr_e
  bindings : Option (SourceToken × NonEmptyArray letBinding_e)
  deriving Repr, BEq

-- 5. LetBinding is the "Sum" of the complex
inductive LetBindingF (e expr_e valueBindingFields_e where_e : Type) where
  | Signature (labeled : Labeled (Name Ident) (Type_ e))
  | Name (fields : valueBindingFields_e)
  | Pattern (binder : Binder e) (token : SourceToken) (where_ : where_e)
  | Error (data : e)
  deriving Repr, BEq

structure CaseOfF (e expr_e guardedRecursive_e : Type) where
  keyword : SourceToken
  head : Separated expr_e
  of : SourceToken
  branches : NonEmptyArray (Separated (Binder e) × guardedRecursive_e)
  deriving Repr, BEq

structure LetInF (e expr_e letBindingRecursive_e : Type) where
  keyword : SourceToken
  bindings : NonEmptyArray letBindingRecursive_e
  in_ : SourceToken
  body : expr_e
  deriving Repr, BEq

inductive DoStatementF (e expr_e letBindingRecursive_e : Type)
  | Let (token : SourceToken) (bindings : NonEmptyArray letBindingRecursive_e)
  | Discard (expr : expr_e)
  | Bind (binder : Binder e) (token : SourceToken) (expr : expr_e)
  | Error (data : e)
  deriving Repr, BEq

structure DoBlockF (e expr_e doStatement_e : Type) where
  keyword : SourceToken
  statements : NonEmptyArray doStatement_e
  deriving Repr, BEq

structure AdoBlockF (e expr_e doStatement_e : Type) where
  keyword : SourceToken
  statements : Array doStatement_e
  in_ : SourceToken
  result : expr_e
  deriving Repr, BEq

inductive ExprF (e expr_e doBlock adoBlock guardedRecursive_e letBindingRecursive_e : Type)
  | Hole (name : Name Ident)
  | Section (token : SourceToken)
  | Ident (name : QualifiedName Ident)
  | Constructor (name : QualifiedName Proper)
  | Boolean (token : SourceToken) (val : Bool)
  | Char (token : SourceToken) (val : Char)
  | NonEmptyString (token : SourceToken) (val : NonEmptyString)
  | Int (token : SourceToken) (val : IntValue)
  | Number (token : SourceToken) (val : Float)
  | Array (items : Delimited expr_e)
  | Record (fields : Delimited (RecordLabeled expr_e))
  | Parens (wrapped : Wrapped expr_e)
  | Typed (expr : expr_e) (token : SourceToken) (type_ : Type_ e)
  | Infix (head : expr_e) (tail : NonEmptyArray (Wrapped expr_e × expr_e))
  | Op (head : expr_e) (ops : NonEmptyArray (QualifiedName Operator × expr_e))
  | OpName (name : QualifiedName Operator)
  | Negate (token : SourceToken) (expr : expr_e)
  | RecordAccessor (data : RecordAccessorF expr_e)
  | RecordUpdate (expr : expr_e) (updates : DelimitedNonEmpty (RecordUpdateF e expr_e))
  | App (fn : expr_e) (args : NonEmptyArray (AppSpineF e expr_e))
  | Lambda (data : LambdaF e expr_e)
  | If (data : IfThenElseF expr_e)
  | Case (data : CaseOfF e expr_e guardedRecursive_e)
  | Let (data : LetInF e expr_e letBindingRecursive_e)
  | Do (data : doBlock)
  | Ado (data : adoBlock)
  | Error (data : e)
  deriving Repr, BEq

-- https://github.com/leanprover/lean4/issues/13465#issuecomment-4349653768
-- mutual

-- inductive LetBindingRecursive (e : Type) where
--   | mk : LetBindingF e (Expr e)
--       (ValueBindingFieldsRecursive e)
--       (WhereRecursive e)
--     → LetBindingRecursive e
--   deriving Repr, BEq

-- inductive WhereRecursive (e : Type) where
--   | mk : WhereF e (Expr e) (LetBindingRecursive e) → WhereRecursive e
--   deriving Repr, BEq

-- inductive GuardedRecursive (e : Type) where
--   | mk : GuardedF e (Expr e)
--       (WhereRecursive e)
--       (GuardedRecursive e)
--     → GuardedRecursive e
--   deriving Repr, BEq

-- inductive ValueBindingFieldsRecursive (e : Type) where
--   | mk : ValueBindingFieldsF e (Expr e) (GuardedRecursive e)
--     → ValueBindingFieldsRecursive e
--   deriving Repr, BEq

-- inductive DoStatementRecursive (e : Type)
--   | mk : DoStatementF e (Expr e) (LetBindingRecursive e) → DoStatementRecursive e
--   deriving Repr, BEq

-- inductive DoBlockRecursive (e : Type)
--   | mk : DoBlockF e (Expr e) (DoStatementRecursive e) → DoBlockRecursive e
--   deriving Repr, BEq

-- inductive AdoBlockRecursive (e : Type)
--   | mk : AdoBlockF e (Expr e) (DoStatementRecursive e) → AdoBlockRecursive e
--   deriving Repr, BEq

-- inductive Expr (e : Type)
--   | mk : ExprF e (Expr e) (DoBlockRecursive e) (AdoBlockRecursive e) (LetBindingRecursive e) (GuardedRecursive e) → Expr e
--   deriving Repr, BEq
-- end
-----------------------------------------------------------------------------------------------------------

-- inductive InstanceBinding (e : Type)
--   | Signature (labeled : Labeled (Name Ident) (Type_ e))
--   | Name (fields : ValueBindingFieldsRecursive e)
--   deriving Repr, BEq

-- structure Instance (e : Type) where
--   head : InstanceHead e
--   body : Option (SourceToken × NonEmptyArray (InstanceBinding e))
--   deriving Repr, BEq

inductive Foreign (e : Type)
  | Value (labeled : Labeled (Name Ident) (Type_ e))
  | Data (keyword : SourceToken) (labeled : Labeled (Name Proper) (Type_ e))
  | Kind (keyword : SourceToken) (name : Name Proper)
  deriving Repr, BEq

inductive Fixity
  | Infix
  | Infixl
  | Infixr
  deriving Repr, BEq, Ord

inductive FixityOp
  | Value (name : QualifiedName (Ident ⊕ Proper)) (token : SourceToken) (op : Name Operator)
  | Type_ (token1 : SourceToken) (name : QualifiedName Proper) (token2 : SourceToken) (op : Name Operator)
  deriving Repr, BEq

structure FixityFields where
  keyword : SourceToken × Fixity
  prec : SourceToken × USize
  operator : FixityOp
  deriving Repr, BEq

inductive Role
  | Nominal
  | Representational
  | Phantom
  deriving Repr, BEq, Ord

-- inductive Declaration (e : Type)
--   | Data (head : DataHead e) (optionSeparator : Option (SourceToken × (Separated (DataCtor e))))
--   | Type_ (head : DataHead e) (token : SourceToken) (type_ : Type_ e)
--   | Newtype (head : DataHead e) (token : SourceToken) (name : Name Proper) (type_ : Type_ e)
--   | Class (head : ClassHead e) (optionSeparator : Option (SourceToken × NonEmptyArray (Labeled (Name Ident) (Type_ e))))
--   | InstanceChain (separated : Separated (Instance e))
--   | Derive (keyword : SourceToken) (optionToken : Option SourceToken) (head : InstanceHead e)
--   | KindSignature (token1 : SourceToken) (labeled : Labeled (Name Proper) (Type_ e))
--   | Signature (labeled : Labeled (Name Ident) (Type_ e))
--   | Value (fields : ValueBindingFieldsRecursive e)
--   | Fixity (fields : FixityFields)
--   | Foreign (token1 : SourceToken) (token2 : SourceToken) (foreign : Foreign e)
--   | Role (token1 : SourceToken) (token2 : SourceToken) (name : Name Proper) (roles : NonEmptyArray (SourceToken × Role))
--   | Error (data : e)
--   deriving Repr, BEq

-----------------------------------------------------------------------------------------------------------

inductive Import (e : Type)
  | Value (name : Name Ident)
  | Op (name : Name Operator)
  | Type_ (name : Name Proper) (optionMembers : Option DataMembers)
  | TypeOp (token : SourceToken) (name : Name Operator)
  | Class (token : SourceToken) (name : Name Proper)
  | Error (data : e)
  deriving Repr, BEq

structure ImportDecl (e : Type) where
  keyword : SourceToken
  module_ : Name ModuleName
  importList : Option (Option SourceToken × DelimitedNonEmpty (Import e))
  qualified : Option (SourceToken × Name ModuleName)
  deriving Repr, BEq
-----------------------------------------------------------------------------------------------------------

structure ModuleHeader (e : Type) where
  keyword : SourceToken
  name : Name ModuleName
  exports : Option (DelimitedNonEmpty (Export e))
  where_ : SourceToken
  imports : Array (ImportDecl e)
  deriving Repr, BEq

-- structure ModuleBody (e : Type) where
--   decls : Array (Declaration e)
--   trailingComments : Array (Comment LineFeed)
--   end_ : SourcePos
--   deriving Repr, BEq

-- structure Module (e : Type) where
--   header : ModuleHeader e
--   body : ModuleBody e
--   deriving Repr, BEq

end PureScript.CST.Types
