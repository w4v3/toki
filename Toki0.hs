import qualified Data.ByteString.Lazy as B
import Data.Word
import Data.Maybe
import Control.Monad
import GHC.IO

data Ki = E | Leaf Word8 | Node Ki Ki
data KiPat = PatLeaf Word8 | Var Integer | LeafVar Integer | PatNode KiPat KiPat

toChar :: Word8 -> Char
toChar = toEnum . fromEnum

--instance Show Ki where
--  show (Leaf x) = "Leaf " ++ show (toChar x)
--  show (Node t1 t2) = "Node (" ++ show t1 ++ ") (" ++ show t2 ++ ")"

instance Show Ki where
  show (Leaf x) | toChar x == '{' = "\\{"
                | toChar x == '}' = "\\}"
                | otherwise = pure $ toChar x
  show (Node n@(Node _ _) t) = "{" ++ show n ++ "}" ++ show t
  show (Node l t) = show l ++ show t

instance Show KiPat where
  show (PatLeaf x) = "PatLeaf " ++ show (toChar x)
  show (PatNode t1 t2) = "PatNode (" ++ show t1 ++ ") (" ++ show t2 ++ ")"
  show (Var x) = "Var " ++ show x
  show (LeafVar x) = "LeafVar " ++ show x

data MatchSym = MLeaf | MNode | MLeafVar | MVar | MLeafVal Word8 | MInd Integer deriving Eq
data RuleStore = RS [(MatchSym,RuleStore)] | L KiPat deriving Show
type VarStore = [(Integer,Ki)]

instance Show MatchSym where
  show MLeaf = "MLeaf"
  show MNode = "MNode"
  show MLeafVar = "MLeafVar"
  show MVar = "MVar"
  show (MLeafVal x) = "MLeafVal " ++ show (toChar x)
  show (MInd x) = "MInd " ++ show x

match :: RuleStore -> RuleStore -> VarStore -> [Ki] -> Maybe (RuleStore,VarStore,Maybe Ki)
match ors (RS rs) vs [(Leaf n)] = do (RS rs') <- lookup MLeaf rs
                                     rs'' <- lookup (MLeafVal n) rs'
                                     match ors rs'' vs []
                                  `mplus`
                                  do (RS rs') <- lookup MLeafVar rs
                                     let (MInd i,rs'') = head rs'
                                     match ors rs'' ((i,Leaf n):vs) []
                                  `mplus`
                                  do (RS rs') <- lookup MVar rs
                                     let (MInd i,rs'') = head rs'
                                     match ors rs'' ((i,Leaf n):vs) []
match ors (RS rs) vs [(Node t1 t2)] = do rs' <- lookup MNode rs 
                                         match ors rs' vs [t1,t2]
                                      `mplus`
                                      do (RS rs') <- lookup MVar rs
                                         let (MInd i,rs'') = head rs'
                                         match ors rs'' ((i,Node t1 t2):vs) []
match ors rs vs [t2,E] = case match ors rs vs [t2] of
                           r@(Just _) -> r
                           _ -> unsafePerformIO (putStrLn ("reducing " ++ show t2) >> return (reduceStep ors t2 >>= match ors rs vs . (:[E])))
                           --_ -> reduceStep ors t2 >>= match ors rs vs . (:[E])
match ors rs vs [t1,t2] = case match ors rs vs [t1] of
                            Just (rs',vs',Nothing) -> match ors rs' vs' [t2,E]
                            _ -> Nothing
                            --_ -> unsafePerformIO (putStrLn ("reducing " ++ show t1) >> return (reduceStep ors t1 >>= match ors rs vs . (:[t2])))
                            --_ -> reduceStep ors t1 >>= match ors rs vs . (:[t2])
match ors (L p) vs [] = Just (RS [],[],Just $ substitute vs p)
match ors (RS rs) vs [] = Just (RS rs,vs,Nothing)

substitute :: VarStore -> KiPat -> Ki
substitute vs (PatLeaf x) = Leaf x
substitute vs (Var x) = fromJust $ lookup x vs
substitute vs (LeafVar x) = fromJust $ lookup x vs
substitute vs (PatNode p1 p2) = Node (substitute vs p1) (substitute vs p2)

reduceStep :: RuleStore -> Ki -> Maybe Ki
reduceStep rs t = case match rs rs [] [t] of
                       Just (_,_,Just t') -> Just t'
                       _ -> Nothing

reduce :: RuleStore -> Ki -> Ki
reduce rs t = unsafePerformIO (print t >> return (case reduceStep rs t of
                Nothing -> t
                Just t' -> reduce rs t'))

--data KiPat = PatLeaf Word8 | Var Integer | LeafVar Integer | PatNode KiPat KiPat
--data MatchSym = MLeaf | MNode | MLeafVar | MVar | MLeafVal Word8 | MInd Integer deriving Eq
--
insert :: Eq a => a -> b -> [(a,b)] -> [(a,b)]
insert k v = ((k,v):)

-- exists -> insert/update/error/ignore
-- does not exist -> insert/error/ignore

update :: Eq a => a -> b -> [(a,b)] -> [(a,b)]
update k v = map (\(k',v') -> if k == k' then (k,v) else (k',v'))

insertOrAppend :: RuleStore -> MatchSym -> MatchSym -> RuleStore -> RuleStore
insertOrAppend (RS rs) s1 s2 r = case lookup s1 rs of
                                   Nothing -> RS ((s1,RS [(s2,r)]):rs)
                                   Just (RS rs') -> RS $ update s1 (RS ((s2,r):rs')) rs

serialize :: KiPat -> RuleStore -> RuleStore
serialize (PatLeaf n) r = RS [(MLeaf,RS [(MLeafVal n,r)])]
serialize (Var n) r = RS [(MVar,RS [(MInd n,r)])]
serialize (LeafVar n) r = RS [(MLeafVar,RS [(MInd n,r)])]
serialize (PatNode p1 p2) r = RS [(MNode,serialize p1 (serialize p2 r))]

updateRuleStore :: RuleStore -> RuleStore -> RuleStore
updateRuleStore (RS rs) (RS [(r,rs')]) = case lookup r rs of
                                           Nothing -> RS ((r,rs'):rs)
                                           Just rs'' -> RS $ update r (updateRuleStore rs'' rs') rs
updateRuleStore (L p) r = r

--storeRule' :: RuleStore -> KiPat -> RuleStore -> RuleStore
--storeRule' (RS rs) (PatLeaf n) r = insertOrAppend (RS rs) MLeaf (MLeafVal n) r
--storeRule' (RS rs) (Var n) r = insertOrAppend (RS rs) MVar (MInd n) r
--storeRule' (RS rs) (LeafVar n) r = insertOrAppend (RS rs) MLeafVar (MInd n) r
--storeRule' (RS rs) (PatNode p1 p2) r = case lookup MNode rs of
--                                         Nothing -> RS ((MNode,storeRule' (RS []) p1 (storeRule' (RS []) p2 r)):rs)
--                                         Just (RS rs') -> RS $ update MNode (RS ((s2,r):rs')) rs

storeRule :: RuleStore -> KiPat -> KiPat -> RuleStore
--storeRule rs l r = storeRule' rs l (L r)
storeRule rs l r = updateRuleStore rs $ serialize l (L r)

storeRules :: [(KiPat,KiPat)] -> RuleStore
storeRules = foldr (rearrange storeRule) (RS []) 
  where rearrange f (x,y) z = f z x y

listKi :: [Word8] -> Ki
listKi = foldr (Node . Leaf) (Leaf 00)

sym :: String -> Ki
sym = listKi . map (toEnum . fromEnum)

lit :: Char -> Ki
lit = Leaf . toEnum . fromEnum

empty :: Ki
empty = Leaf 00

pempty :: KiPat
pempty = PatLeaf 00

pattify :: Ki -> KiPat
pattify (Leaf x) = PatLeaf x
pattify (Node t1 t2) = PatNode (pattify t1) (pattify t2)

rules :: RuleStore
rules = storeRules
        [
          (PatNode (pattify $ lit '{') (Var 0),PatNode (pattify $ sym "bgroup") (PatNode pempty (Var 0)))
        , (PatNode (pattify $ sym "bgroup") (PatNode (Var 0) (PatNode (pattify $ lit '}') (Var 1))),PatNode (pattify $ sym "parsed") (PatNode (Var 0) (Var 1)))
        , (PatNode (pattify $ sym "bgroup") (PatNode (Var 0) (PatNode (pattify $ sym "parsed") (PatNode (Var 1) (Var 2)))),PatNode (pattify $ sym "bgroup") (PatNode (PatNode (Var 1) (Var 0)) (Var 2)))
        , (PatNode (LeafVar 0) (Var 1),PatNode (pattify $ sym "parsed") (PatNode (Var 0) (Var 1)))
        , (PatNode (pattify $ sym "parsed") (PatNode (Var 0) (Var 1)),Var 1)
        --, (pattify $ lit '[', pattify $ lit '{')
        --, (pattify $ lit ']', pattify $ lit '}')
        --, (PatNode (pattify $ lit '[') (Var 0), (PatNode (pattify $ lit '{') (Var 0)))
        --, (PatNode (pattify $ lit ']') (Var 0), (PatNode (pattify $ lit '}') (Var 0)))
        ]

--rules' = storeRules
--        [
--          (PatNode (pattify $ lit '{') (Var 0),PatNode (pattify $ sym "bgroup") (PatNode pempty (Var 0)))
--        , (PatNode (pattify $ sym "bgroup") (PatNode (Var 0) (PatNode (pattify $ lit '}') (Var 1))),PatNode (PatNode (Var 0) $ pattify $ sym "parsed") (Var 1))
--        , (PatNode (pattify $ sym "bgroup") (PatNode (Var 0) (PatNode (PatNode (Var 1) $ pattify $ sym "parsed") ((Var 2)))),PatNode (pattify $ sym "bgroup") (PatNode (PatNode (Var 1) (Var 0)) (Var 2)))
--        , (PatNode (LeafVar 0) (Var 1),PatNode (PatNode (Var 0) $ pattify $ sym "parsed") ((Var 1)))
--        , (PatNode (PatNode (Var 0) $ pattify $ sym "parsed") ((Var 1)),Var 1)
--        ]
--
--rules'' = storeRules
--        [
--          (PatNode (pattify $ lit '{') (Var 0),PatNode (pattify $ sym "bgroup") (PatNode pempty (Var 0)))
--        , (PatNode (pattify $ sym "bgroup") (PatNode (Var 0) (PatNode (pattify $ lit '}') (Var 1))),PatNode (pattify $ sym "parsed") (PatNode (Var 0) (Var 1)))
--        , (PatNode (pattify $ lit '[') (Var 0),PatNode (pattify $ sym "bgroup") (PatNode pempty (Var 0)))
--        , (PatNode (pattify $ sym "bgroup") (PatNode (Var 0) (PatNode (pattify $ lit ']') (Var 1))),PatNode (pattify $ sym "parsed") (PatNode (Var 0) (Var 1)))
--        , (PatNode (pattify $ sym "bgroup") (PatNode (Var 0) (PatNode (pattify $ sym "parsed") (PatNode (Var 1) (Var 2)))),PatNode (pattify $ sym "bgroup") (PatNode (PatNode (Var 1) (Var 0)) (Var 2)))
--        , (PatNode (LeafVar 0) (Var 1),PatNode (pattify $ sym "parsed") (PatNode (Var 0) (Var 1)))
--        , (PatNode (pattify $ sym "parsed") (PatNode (Var 0) (Var 1)),Var 1)
--        ]

--match :: [(KiPat,KiPat)] -> KiPat -> Ki -> Maybe [(Integer,Ki)]
--match rs (PatLeaf x) (Leaf y) | x == y = Just []
--                              | otherwise = Nothing
--match rs (Var x) t = Just [(x,t)]
--match rs (LeafVar x) t@(Leaf _) = Just [(x,t)]
--match rs (PatNode p1 p2) (Node t1 t2) = (++) 
--                                     <$> tryReduce rs p1 t1
--                                     <*> tryReduce rs p2 t2
--match rs _ _ = Nothing
--
--tryReduce :: [(KiPat,KiPat)] -> KiPat -> Ki -> Maybe [(Integer,Ki)]
--tryReduce rs p t = case match rs p t of
--                     Nothing -> case reduceStep rs t of
--                                  Nothing -> Nothing
--                                  Just x -> tryReduce rs p x
--                     Just x -> Just x
--rewrite :: [(KiPat,KiPat)] -> KiPat -> KiPat -> Ki -> Maybe Ki
--rewrite rs l r t = match rs l t >>= return . flip substitute r

--reduceStep rs t = msum $ map (flip (uncurry $ rewrite rs) t) rs

cantor :: Int -> String
cantor 0 = "{}"
cantor n = "{" ++ cantor (n-1) ++ "}" ++ cantor (n-1)
