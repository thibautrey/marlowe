{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE ViewPatterns      #-}

-- | Handles finding imports and compiling them recursively.
-- This is done for each full AST traversal the copmiler does
-- which at this point is InitialPass's preprocessing
-- and Compiler's code generation
module Fay.Compiler.Import
  ( startCompile
  , startCompileText
  , compileWith
  ) where

import           Fay.Compiler.Prelude

import           Fay.Compiler.Misc
import           Fay.Compiler.Parse
import           Fay.Config
import qualified Fay.Exts                        as F
import           Fay.Exts.NoAnnotation           (unAnn)
import           Fay.Types

import           Control.Monad.Except            (throwError)
import           Control.Monad.RWS               (ask, get, gets, lift, listen, modify)
import           Language.Haskell.Exts hiding (name)
import           System.Directory
import           System.FilePath

-- | Start the compilation process using `compileModule` to compile a file.
startCompile :: (FilePath -> String -> Compile a) -> FilePath -> Compile a
startCompile compileModule filein = do
  modify $ \s -> s { stateImported = [] }
  fmap fst . listen $ compileModuleFromFile compileModule filein

startCompileText :: (FilePath -> String -> Compile a) -> FilePath -> String -> Compile a
startCompileText compileModule filein string = do
  modify $ \s -> s { stateImported = [] }
  compileModule filein string

-- | Compile a module
compileWith
  :: Monoid a
  => FilePath
  -> (a -> F.Module -> Compile a)
  -> (FilePath -> String -> Compile a)
  -> (F.X -> F.Module -> IO (Either CompileError F.Module))
  -> String
  -> Compile (a, CompileState, CompileWriter)
compileWith filepath with compileModule before from = do
  rd <- ask
  st <- get
  res <- Compile . lift . lift $
    runCompileModule
      rd
      st
      (parseResult (throwError . uncurry ParseError)
                   (\mod' -> do
                     mod@(Module _ _ _ imports _) <-
                       either throwError return =<< io (before F.noI mod')
                     res <- foldr (<>) mempty <$> mapM (compileImport compileModule) imports
                     modify $ \s -> s { stateModuleName = unAnn $ F.moduleName mod }
                     with res mod
                   )
                   (parseFay filepath from))
  either throwError return res

-- | Compile a module given its file path
compileModuleFromFile
  :: (FilePath -> String -> Compile a)
  -> FilePath
  -> Compile a
compileModuleFromFile compileModule fp = io (readFile fp) >>= compileModule fp

-- | Lookup a module from include directories and compile.
compileModuleFromName
  :: Monoid a
  => (FilePath -> String -> Compile a)
  -> F.ModuleName
  -> Compile a
compileModuleFromName compileModule nm =
  unlessImported nm compileModule
    where
      unlessImported
        :: Monoid a
        => ModuleName l
        -> (FilePath -> String -> Compile a)
        -> Compile a
      unlessImported (ModuleName _ "Fay.Types") _ = return mempty
      unlessImported (unAnn -> name) importIt = do
        imported <- gets stateImported
        case lookup name imported of
          Just _  -> return mempty
          Nothing -> do
            dirs <- configDirectoryIncludePaths <$> config id
            (filepath,contents) <- findImport dirs name
            modify $ \s -> s { stateImported = (name,filepath) : imported }
            importIt filepath contents

-- | Compile an import.
compileImport
  :: Monoid a
  => (FilePath -> String -> Compile a)
  -> F.ImportDecl
  -> Compile a
compileImport compileModule i = case i of
  -- Trickery in fay-base needs this special case
  ImportDecl _ _    _ _ _ (Just "base") _ _ -> return mempty
  ImportDecl _ name _ _ _ _ _ _ -> compileModuleFromName compileModule name

-- | Find an import's filepath and contents from its module name.
findImport :: [FilePath] -> ModuleName a -> Compile (FilePath,String)
findImport alldirs (unAnn -> mname) = go alldirs mname where
  go :: [FilePath] -> ModuleName a -> Compile (FilePath,String)
  go _ (ModuleName _ "Fay.FFI") = return ("Fay/FFI.hs", "module Fay.FFI where\n\ndata Nullable a = Nullable a | Null\n\ndata Defined a = Defined a | Undefined")
  go _ (ModuleName _ "Types") = return ("Fay/Types.hs", "newtype Fay a = Fay (Identity a)\n\nnewtype Identity a = Identity a")
  go _ (ModuleName _ "Data.Data") = return ("Data/Data.hs", "{-# LANGUAGE PackageImports #-}\n{-# LANGUAGE NoImplicitPrelude #-}\n{-# LANGUAGE CPP #-}\nmodule Data.Data\n#ifndef FAY\n  (Data,Typeable)\n#endif\n  where\n\nimport \"base\" Data.Data\n") 
  go _ (ModuleName _ "Prelude") = return ("Prelude.hs", "{-# LANGUAGE CPP                  #-}\n{-# LANGUAGE FlexibleInstances    #-}\n{-# LANGUAGE PackageImports       #-}\n{-# LANGUAGE TypeSynonymInstances #-}\n{-# OPTIONS -fno-warn-missing-methods #-}\n\nmodule Prelude\n  (\n  -- Prelude type re-exports\n   Base.Char\n  ,Base.String\n  ,Base.Double\n  ,Base.Int\n  ,Base.Integer\n  ,Base.Bool(..)\n  ,Base.Read\n  ,Base.Show\n  ,Base.Eq\n  ,(==)\n  ,(/=)\n  -- Standard data types\n  ,Maybe(..)\n  ,maybe\n  -- Monads\n  ,(>>=)\n  ,(>>)\n  ,return\n  ,fail\n  ,when\n  ,unless\n  ,forM\n  ,forM_\n  ,mapM\n  ,mapM_\n  ,(=<<)\n  ,sequence\n  ,sequence_\n  ,void\n  ,(>=>)\n  ,(<=<)\n  -- Num\n  ,(*)\n  ,(+)\n  ,(-)\n  -- Ord\n  ,Ord\n  ,Ordering(..)\n  -- An ordering.\n  ,(<)\n  ,(<=)\n  ,(>)\n  ,(>=)\n  ,compare\n  -- Enum\n  ,succ\n  ,pred\n  ,enumFrom\n  ,enumFromTo\n  ,enumFromBy\n  ,enumFromThen\n  ,enumFromByTo\n  ,enumFromThenTo\n  -- Fractional\n  ,(/)\n  -- Integral\n  ,fromIntegral\n  ,fromInteger\n  -- Bools\n  ,(&&)\n  ,(||)\n  ,not\n  ,otherwise\n  -- Show\n  ,show\n  -- Errors\n  ,error\n  ,undefined\n  ,Either(..)\n  ,either\n  -- Functions\n  ,until\n  ,($!)\n  ,seq\n  ,const\n  ,id\n  ,(.)\n  ,($)\n  ,flip\n  ,curry\n  ,uncurry\n  ,snd\n  ,fst\n  -- Numbers\n  ,div\n  ,mod\n  ,divMod\n  ,min\n  ,max\n  ,recip\n  ,negate\n  ,abs\n  ,signum\n  ,pi\n  ,exp\n  ,sqrt\n  ,log\n  ,(**)\n  ,(^^)\n  ,unsafePow\n  ,(^)\n  ,logBase\n  ,sin\n  ,tan\n  ,cos\n  ,asin\n  ,atan\n  ,acos\n  ,sinh\n  ,tanh\n  ,cosh\n  ,asinh\n  ,atanh\n  ,acosh\n  ,properFraction\n  ,truncate\n  ,round\n  ,ceiling\n  ,floor\n  ,subtract\n  ,even\n  ,odd\n  ,gcd\n  ,quot\n  ,quot'\n  ,quotRem\n  ,rem\n  ,rem'\n  ,lcm\n  -- Lists\n  ,find\n  ,filter\n  ,null\n  ,map\n  ,nub\n  ,nub'\n  ,elem\n  ,notElem\n  ,sort\n  ,sortBy\n  ,insertBy\n  ,conc\n  ,concat\n  ,concatMap\n  ,foldr\n  ,foldr1\n  ,foldl\n  ,foldl1\n  ,(++)\n  ,(!!)\n  ,head\n  ,tail\n  ,init\n  ,last\n  ,iterate\n  ,repeat\n  ,replicate\n  ,cycle\n  ,take\n  ,drop\n  ,splitAt\n  ,takeWhile\n  ,dropWhile\n  ,span\n  ,break\n  ,zipWith\n  ,zipWith3\n  ,zip\n  ,zip3\n  ,unzip\n  ,unzip3\n  ,lines\n  ,unlines\n  ,words\n  ,unwords\n  ,and\n  ,or\n  ,any\n  ,all\n  ,intersperse\n  ,prependToAll\n  ,intercalate\n  ,maximum\n  ,minimum\n  ,product\n  ,sum\n  ,scanl\n  ,scanl1\n  ,scanr\n  ,scanr1\n  ,lookup\n  ,length\n  ,length'\n  ,reverse\n  -- IO\n  ,print\n  ,putStrLn\n  ,ifThenElse\n  ,Fay\n  )\n  where\n\n#ifdef FAY\nimport           Data.Data\n#endif\nimport           Fay.FFI\nimport           \"base\" Prelude   (Bool (True, False), Eq, seq, (&&), (/=),\n                                   (==), (||))\nimport qualified \"base\" Prelude   as Base\n#ifndef FAY\nimport           \"base\" Prelude   (Either (..), Maybe (..), Ordering (..))\n#endif\n\n--------------------------------------------------------------------------------\n-- Fixities\n\ninfixr 9  .\ninfixr 8  ^, ^^, **\ninfixl 7  *, /, `quot`, `rem`, `div`, `mod`\ninfixl 6  +, -\n\n-- The (:) operator is built-in syntax, and cannot legally be given\n-- a fixity declaration; but its fixity is given by:\n--   infixr 5  :\n\n-- Provided by base prelude\n--   infix  4  ==, /=\n--   infixr 3  &&\n--   infixr 2  ||\n--   infixr 0  $, $!\n\ninfixr 4  <, <=, >=, >\ninfixl 1  >>, >>=\ninfixr 1  =<<, >=>, <=<\ninfixr 0  $, $!\n\n-- PreludeList\n\ninfixl 9  !!\ninfixr 5  ++\ninfix  4  `elem`, `notElem`\n\n--------------------------------------------------------------------------------\n-- Aliases of base\n\ntype Char    = Base.Char\ntype Double  = Base.Double\ntype Int     = Base.Int\ntype Integer = Base.Integer\ntype String  = Base.String\n\n--------------------------------------------------------------------------------\n-- Standard data types\n\n-- | Maybe type.\n#ifdef FAY\ndata Maybe a = Just a | Nothing\ninstance Base.Read a => Base.Read (Maybe a)\ninstance Base.Show a => Base.Show (Maybe a)\ninstance Typeable a => Typeable (Maybe a)\ninstance Data a => Data (Maybe a)\n#endif\n\n-- | Either type.\n#ifdef FAY\ndata Either a b = Left 
  go _ (ModuleName _ "Marlowe") = return ("Marlowe.hs", "module Marlowe(Money(..), Observation(..), Contract(..), Person, Random, BlockNumber, Cash, ConcreteChoice, Timeout, IdentCC(..), IdentChoice(..), IdentPay(..), prettyPrintContract) where\n\n-- Standard library functions\n\ngroupBy                 :: (a -> a -> Bool) -> [a] -> [[a]]\ngroupBy _  []           =  []\ngroupBy eq (x:xs)       =  (x:ys) : groupBy eq zs\n                           where (ys,zs) = span (eq x) xs\n\n -- People are represented by their public keys,\n -- which in turn are given by integers.\n\ntype Key         = Int   -- Public key\ntype Person      = Key\n\n-- Block numbers and random numbers are both integers.\n \ntype Random      = Int\ntype BlockNumber = Int\n\n-- Observables are things which are recorded on the blockchain.\n--  e.g. \"a random choice\", the value of GBP/BTC exchange rate, \8230\n\n-- Question: how do we implement these things?\n--  - We assume that some mechanism exists which will ensure that the value is looked up and recorded, or \8230\n--  - \8230 we actually provide that mechanism explicitly, e.g. with inter-contract comms or transaction generation or something.\n\n-- Other observables are possible, e.g. the value of the oil price at this time.\n-- It is assumed that these would be provided in some agreed way by an oracle of some sort.\n\n-- The Observable data type represents the different sorts of observables, \8230\n\ndata Observable = Random | BlockNumber\n                    deriving (Eq)\n\nshowObservable Random = \"Random\"\nshowObservable BlockNumber = \"BlockNumber\"\n\n-- Inputs\n-- Types for cash commits, money redeems, and choices.\n--\n-- A cash commitment is an integer (should be positive integer?)\n-- Concrete values are sometimes chosen too: these are integers for the sake of this model.\n\ntype Cash     = Int\ntype ConcreteChoice = Int\n\n-- We need to put timeouts on various operations. These could be some abstract time\n-- domain, but it only really makes sense for these to be block numbers.\n\ntype Timeout = BlockNumber\n\n-- Commitments, choices and payments are all identified by identifiers.\n-- Their types are given here. In a more sophisticated model these would\n-- be generated automatically (and so uniquely); here we simply assume that \n-- they are unique.\n\nnewtype IdentCC = IdentCC Int\n               deriving (Eq)\n\nnewtype IdentChoice = IdentChoice Int\n               deriving (Eq)\n\nnewtype IdentPay = IdentPay Int\n               deriving (Eq)\n\n-- Money is a set of contract primitives that represent constants,\n-- functions, and variables that can be evaluated as an ammount\n-- of money.\n\ndata Money = AvailableMoney IdentCC |\n             AddMoney Money Money |\n             ConstMoney Cash |\n             MoneyFromChoice IdentChoice Person Money\n                    deriving (Eq)\n\nshowMoney :: Money -> String\nshowMoney (AvailableMoney (IdentCC icc)) = \"(AvailableMoney (IdentCC \" ++ show icc ++ \"))\"\nshowMoney (AddMoney m1 m2) = \"(AddMoney \" ++ showMoney m1 ++ \" \" ++ showMoney m2 ++ \")\"\nshowMoney (ConstMoney cash) = \"(ConstMoney \" ++ show cash ++ \")\"\nshowMoney (MoneyFromChoice (IdentChoice ic) p m) = \"(MoneyFromChoice (IdentChoice \" ++ show ic ++ \") \" ++ show p ++ \" \" ++ showMoney m ++ \")\"\n\n-- Representation of observations over observables and the state.\n-- Rendered into predicates by interpretObs.\n\ndata Observation =  BelowTimeout Timeout | -- are we still on time for something that expires on Timeout?\n                    AndObs Observation Observation |\n                    OrObs Observation Observation |\n                    NotObs Observation |\n                    PersonChoseThis IdentChoice Person ConcreteChoice |\n                    PersonChoseSomething IdentChoice Person |\n                    ValueGE Money Money | -- is first ammount is greater or equal than the second?\n                    TrueObs | FalseObs\n                    deriving (Eq)\n\nshowObservation :: Observation -> String\nshowObservation (BelowTimeout tim) = \"(BelowT
  go (dir:dirs) name = do
    exists <- io (doesFileExist path)
    if exists
           then (path,) . stdlibHack <$> io (readFile path)
           else go dirs name
    where
      path = dir </> replace '.' '/' (prettyPrint name) ++ ".hs"
      stdlibHack = case mname of
                     ModuleName _ "Fay.FFI" -> const "module Fay.FFI where\n\ndata Nullable a = Nullable a | Null\n\ndata Defined a = Defined a | Undefined"
                     _ -> id 
      replace c r = map (\x -> if x == c then r else x)
  go [] name = throwError $ Couldn'tFindImport (unAnn name) alldirs





