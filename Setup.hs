import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.PackageDescription
import System.Cmd
import System.FilePath
import System.Directory
import System.IO.Error


main = defaultMainWithHooks hooks
  where hooks = simpleUserHooks { runTests = runTests'}


hpcReportDir = "hpcreport"

runTests' :: Args -> Bool -> PackageDescription -> LocalBuildInfo -> IO ()
runTests' _ _ _ lbi = do
  res <- try (removeFile tixFile)
  case res of
    Left err
        | not (isDoesNotExistError err) -> putStrLn "tix file could not be removed"
    _ -> return ()
  putStrLn "running tests ..."
  system testprog
  putStrLn "computing code coverage ..."
  hpcReport
  putStrLn "generating code coverage reports ..."
  hpcMarkup
  return ()
    where testprog = (buildDir lbi) </> "test" </> "test"
          tixFile = "test.tix"
          hpcReport = system $ "hpc report test"++exclArgs
          hpcMarkup = system $ "hpc markup test --destdir="++hpcReportDir++exclArgs
          excludedModules = []
          exclArgs = concatMap (" --exclude="++) excludedModules