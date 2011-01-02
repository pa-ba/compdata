{-# LANGUAGE TemplateHaskell #-}

module DataTypes where

import Data.Map (Map)
import Data.ALaCarte.Derive

-- base values

-- |The name of a record.
type RecordName = String

-- |The name of a field in a record.
type FieldName = String

-- |A set of record fields.
data VFields e = VFields (Map FieldName (VField e))
                 deriving (Eq, Ord, Show, Read)

-- |A record.
data VRecord e = VR{
      vrecordName :: RecordName, -- ^The name (type) of the record.
      vrecordFields :: VFields e -- ^The fields of the record.
    } deriving (Eq, Ord, Show, Read)

-- |A record field.
data VField e = VF{
      vfieldName :: FieldName, -- ^The name of the field.
      vfieldValue :: e -- ^The value of the field.
    } deriving (Eq, Ord, Show, Read)

data VDuration a = VD {
      durationSeconds :: a,
      durationMinutes :: a,
      durationHours :: a,
      durationDays :: a,
      durationWeeks :: a,
      durationMonths :: a,
      durationYears :: a
    }
                   deriving (Eq, Ord, Show, Read)

-- |The AST for values.
data Value e = VInt Int -- ^Integer value.
             | VBool Bool -- ^Boolean value.
             | VString String -- ^String value.
             | VDateTime Int -- ^Date value.
             | VDuration (VDuration Int) -- ^Duration value.
             | VDouble Double -- ^Double value.
             | VRecord (VRecord e) -- ^Record value.
             | VList [e] -- ^List value.
               deriving (Eq, Ord, Show, Read)

$(derive [instanceFunctor] [''VField,''VFields,''VRecord,''Value])

-- reporting language extensions


{-| This type represents (value) variable identifiers.  -}

data VVarId = VVarId String Int
    deriving (Eq, Ord, Show, Read)

{-| This data type represents the signature extension for
Parrot values.  -}

data ValueExt e = VVar VVarId     -- ^variable
                | VLam [VVarId] e -- ^lambda abstraction
                | VChar Char      -- ^character value
                | VCons e e       -- ^cons cell
                | VLeft e         -- ^left injection
                | VRight e        -- ^right injection
                | VPair e e       -- ^pairing
                | VUnit           -- ^unit element
    deriving (Eq, Ord, Show, Read)


{-| This data type represents the (optional) time specification of a
date expression. That is, it contains at least two components, the
hours and the minutes, and possibly an additional one representing the
seconds. -}

data TimeExp e = TimeExp {
      timeExpHour :: e,
      timeExpMinute :: e,
      timeExpSecond :: Maybe e
    }
                 deriving (Eq, Ord, Show, Read)



{-| This data type represents the day specification of a date
expression. That is, it has three components representing year, month,
and day respectively. -}

data DayExp e = DayExp {
      dayExpYear :: e,
      dayExpMonth :: e,
      dayExpDay :: e
    }
                deriving (Eq, Ord, Show, Read)



{-| This data type represents the type of a projection (from a product
type).  -}

data Proj = ProjLeft | ProjRight
            deriving (Eq, Ord, Show, Read)


{-| This data type represents a single type case of a type case
distinction as used by ht @type of@ language construct. -}

data TypeCase e = TypeCase { typeCaseRec :: RecordName
                           , typeCaseBody :: e }
                  deriving (Eq, Ord, Show, Read)

data DefTypeCase e = DefTypeCase {defTypeCaseBody :: e}
                  deriving (Eq, Ord, Show, Read)

{-|
  This data type enumerates all build-in binary operators of Parrot.
-}

data BinOpCore = OpPlus
           | OpMinus
           | OpTimes
           | OpDiv
           | OpAnd
           | OpOr
           | OpEq
           | OpNeq
           | OpLt
           | OpLe
           | OpGt
           | OpGe
           | OpDurPlus
           | OpDurMinus
             deriving (Eq, Ord, Show, Read)

{-| This data type represents simple let bindings. -}

data LetBind e = LetBind { letBindVar :: VVarId
                         , letBindArgs :: [VVarId]
                         , letBindBody :: e }
                 deriving (Eq, Ord, Show, Read)

type DurationExp e = VDuration (Maybe e)

data PrimOp = Fold
            | Not
            | Case
            | Error
            | Events
            | LeftOp
            | RightOp
              deriving (Eq, Ord, Show, Read)

{-| This data type represents the extensions to the Parrot core value
signature that then makes up the signature Parrot expressions.  -}

data ExpExt e = App e e
              | BinOpCore e BinOpCore e
              | Let [LetBind e] e
              | TypeOf (Maybe VVarId) e [TypeCase e] (Maybe (DefTypeCase e))
              | RecAcc e FieldName
              | RecMod e [VField e]
              | DateTime (DayExp e) (Maybe (TimeExp e))
              | Duration (DurationExp e)
              | If e e e
              | PrimOp PrimOp
              | Proj e Proj
              deriving (Eq, Ord, Show, Read)

-- translation into regular data types

-- base expressions

type BFields = VField BaseExp

-- |A record.
type BRecord = VRecord BaseExp

-- |A record field.
type BField  = VField BaseExp


-- |The AST for values.
data BaseExp  = BInt Int -- ^Integer value.
              | BBool Bool -- ^Boolean value.
              | BString String -- ^String value.
              | BDateTime Int -- ^Date value.
              | BDuration (VDuration Int) -- ^Duration value.
              | BDouble Double -- ^Double value.
              | BRecord BRecord -- ^Record value.
              | BList [BaseExp] -- ^List value.
               deriving (Eq, Ord, Show, Read)

-- reporting language 

type RFields = VFields RepExp

-- |A record.
type RRecord = VRecord RepExp

-- |A record field.
type RField  = VField RepExp



{-| This data type represents simple let bindings. -}

type RLetBind = LetBind RepExp

{-| This data type represents a single type case of a type case
distinction as used by ht @type of@ language construct. -}

type RTypeCase = TypeCase RepExp

type  RDefTypeCase = DefTypeCase RepExp

type RDayExp = DayExp RepExp

type RTimeExp = TimeExp RepExp

type RDurationExp = DurationExp RepExp

-- |The AST for values.
data RepExp  = RInt Int -- ^Integer value.
              | RBool Bool -- ^Boolean value.
              | RString String -- ^String value.
              | RDateTime Int -- ^Date value.
              | RDuration (VDuration Int) -- ^Duration value.
              | RDouble Double -- ^Double value.
              | RRecord RRecord -- ^Record value.
              | RList [RepExp] -- ^List value
              | RVar VVarId     -- ^variable
              | RLam [VVarId] RepExp -- ^lambda abstraction
              | RChar Char      -- ^character value
              | RCons RepExp RepExp       -- ^cons cell
              | RLeft RepExp         -- ^left injection
              | RRight RepExp        -- ^right injection
              | RPair RepExp RepExp       -- ^pairing
              | RUnit           -- ^unit element.
              | RApp RepExp RepExp
              | RBinOpCore RepExp BinOpCore RepExp
              | RLet [RLetBind] RepExp
              | RTypeOf (Maybe VVarId) RepExp [RTypeCase] (Maybe RDefTypeCase)
              | RRecAcc RepExp FieldName
              | RRecMod RepExp [RField]
              | RDateTimeE RDayExp (Maybe RTimeExp)
              | RDurationE RDurationExp
              | RIf RepExp RepExp RepExp
              | RPrimOp PrimOp
              | RProj RepExp Proj
               deriving (Eq, Ord, Show, Read)