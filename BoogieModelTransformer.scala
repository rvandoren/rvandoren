package viper.carbon.boogie

import viper.carbon.modules.impls.DefaultMainModule

import scala.collection.mutable
import util.control.Breaks._
import viper.carbon.verifier.{Environment, FailureContextImpl}
import viper.silver.verifier.{AbstractError, ApplicationEntry, ConstantEntry, Counterexample, FailureContext, MapEntry, Model, ModelEntry, SimpleCounterexample, UnspecifiedEntry, VerificationError}
import viper.silver.ast.{Exp, LocalVarDecl, Program, Seqn, utility}

import scala.collection.immutable.Map

/**
  * Transforms a counterexample returned by Boogie back to a Viper counterexample.
  */
object BoogieModelTransformer {

  /**
    * Adds a counterexample to the given error if one is available.
    */
  def transformCounterexample(e: AbstractError, names: Map[String, Map[String, String]], program: Program, mm: DefaultMainModule): Unit = {
    if (e.isInstanceOf[VerificationError] && ErrorMemberMapping.mapping.contains(e.asInstanceOf[VerificationError])) {
      //ve just is the condition and the assertion that might not hold
      val ve = e.asInstanceOf[VerificationError]
      val errorMethod = ErrorMemberMapping.mapping.get(ve).get
      // trying to get the types of the method doesn't work
      //      for (lv <- mm.env.allDefinedVariables()) {
      //        println(lv.name)
      //        println(lv.typ)
      //      }
      val typenamesInMethod = names.get(errorMethod.name).get.map(e => e._2 -> e._1)
      val originalEntries = ve.failureContexts(0).counterExample.get.model.entries
      val startKeys = transformModelEntries(originalEntries, typenamesInMethod)


      for ((k,v) <- typenamesInMethod)
        println(s"key: $k, value: $v")
      val workingModel = buildNewModel(originalEntries)
      for ((k, v) <- workingModel)
        println(s"key: $k, value: $v")

//      val (seqOperations, setOperations) = buildTypeModel(workingModel)
//      // Determine all the sequences in the CE
//      // operations before indices???
//      val ceSequences = detSequences(seqOperations)
//      // Determine all the sets in the CE
//      val ceSets = detSets(setOperations)
//
//      var ceBasicTypes = Map[String, Any]()
//      var basicCEheapTypesName = Map[String, String]()
//      for ((name, identifier) <- startKeys) {
//        if (ceSequences.contains(identifier.toString)) {
//          ceBasicTypes += (name -> ceSequences.get(identifier.toString).get)
//        } else if (ceSets.contains(identifier.toString)) {
//          ceBasicTypes += (name -> ceSets.get(identifier.toString).get)
//        } else {
//          basicCEheapTypesName += (name -> identifier.toString)
//        }
//      }
//      val basicCEheapTypesValues = detHeapTypes(workingModel)
//      val basicCounterexample = (ceBasicTypes, basicCEheapTypesName, basicCEheapTypesValues)
//
//      println("All the Sequences:")
//      for ((k, v) <- ceSequences)
//        println(s"Key: $k, Value: $v")
//      println("All the Sets:")
//      for ((k, v) <- ceSets)
//        println(s"Key: $k, Value: $v")
//      println("All the Basic Types:")
//      for ((k,v) <- ceBasicTypes)
//        println(s"Key: $k, Value: $v")
//
//      println("All the Heap Types:")
//      for ((heapInstance, (reference, field), (value, permission)) <- basicCEheapTypesValues)
//        println(s"HI: $heapInstance, Ref: $reference, Field: $field, Value: $value, Perm: $permission")
//
//      val (evalOldHeap, evalRetHeap) = evaluateHT(workingModel, basicCEheapTypesName, basicCEheapTypesValues, program.predicatesByName.keySet, program.fieldsByName.keySet)
//      val finalCounterexample = (ceBasicTypes, evalOldHeap, evalRetHeap)
//
//      println("At old:")
//      for ((name, (value, perm)) <- evalOldHeap)
//        println(s"Name: $name, Value: $value, Perm: $perm")
//      println("On return:")
//      for ((name, (value, perm)) <- evalRetHeap)
//        println(s"Name: $name, Value: $value, Perm: $perm")

      val model = Model(startKeys.toMap)
      println("Model:")
      println(model)
      ve.failureContexts = Seq(FailureContextImpl(Some(SimpleCounterexample(model))))
    }
  }

  /**
    *
    * @param originalEntries Entries of the counterexample produced by Boogie
    * @param namesInMember   Mapping from Boogie names to Viper names for the Viper member belonging to this error.
    * @return
    */
  def transformModelEntries(originalEntries: Map[String, ModelEntry], namesInMember: Map[String, String]): mutable.Map[String, ModelEntry] = {
    val newEntries = mutable.HashMap[String, ModelEntry]()
    val currentEntryForName = mutable.HashMap[String, String]()
    for ((vname, e) <- originalEntries) {
      var originalName = vname
      if (originalName.startsWith("q@")) {
        originalName = originalName.substring(2)
      } else if (originalName.indexOf("@@") != -1) {
        originalName = originalName.substring(0, originalName.indexOf("@@"))
      } else if (originalName.indexOf("@") != -1) {
        originalName = originalName.substring(0, originalName.indexOf("@"))
      }
      if (PrettyPrinter.backMap.contains(originalName)) {
        val originalViperName = PrettyPrinter.backMap.get(originalName).get
        if (namesInMember.contains(originalViperName)) {
          val viperName = namesInMember.get(originalViperName).get
          if (!currentEntryForName.contains(viperName) ||
            isLaterVersion(vname, originalName, currentEntryForName.get(viperName).get)) {
            newEntries.update(viperName, e)
            currentEntryForName.update(viperName, vname)
          }
        }
      }
    }
    newEntries
  }

  /**
    * Heuristically (based on Boogie's naming practices) checks if, of the two Boogie versions of the given
    * original Viper variable name, the first denotes a "later" version (as in, occurring later in the program,
    * therefore containing a more recent value).
    */
  def isLaterVersion(firstName: String, originalName: String, secondName: String): Boolean = {
    if (secondName == originalName || secondName == "q@" + originalName || secondName.indexOf("@@") != -1) {
      true
    } else if (secondName.indexOf("@") != -1 && firstName.indexOf("@@") == -1 && firstName.indexOf("@") != -1) {
      val firstIndex = Integer.parseInt(firstName.substring(firstName.indexOf("@") + 1))
      val secondIndex = Integer.parseInt(secondName.substring(secondName.indexOf("@") + 1))
      firstIndex > secondIndex
    } else {
      false
    }
  }

  // "buildNewModel" builds takes the CE model from Boogie and transforms it into a model which makes it easier to determine the individual values
  def buildNewModel(originalEntries: Map[String, ModelEntry]): Map[Seq[String], String] = {
    var newEntriesMapping = Map[Seq[String], String]()
    for ((key, value) <- originalEntries) {
      if (value.isInstanceOf[ConstantEntry]) {
        val valConstEntry = value.asInstanceOf[ConstantEntry]
        newEntriesMapping += (Seq(key) -> valConstEntry.toString)
      } else if (value.isInstanceOf[MapEntry]) {
        val tempMapping = value.asInstanceOf[MapEntry].options
        for ((keyTM, valueTM) <- tempMapping) {
          val tempSeq = (keyTM.map(x => x.toString))
          if (tempSeq.contains("else")) {
            //
          } else {
            newEntriesMapping += (Seq(key) ++ tempSeq -> valueTM.toString)
          }
        }
      } else if (value.isInstanceOf[ApplicationEntry]) {
        val applEntry = value.asInstanceOf[ApplicationEntry]
        newEntriesMapping += (Seq(key) -> applEntry.toString)
        println((Seq(key) -> applEntry.toString))
      } else if (value.toString != UnspecifiedEntry.toString) {
        println("error in buildNewModel")
      }
    }
    newEntriesMapping
  }

  // "replaceEntriesModel" choose all the operations for specific type supported in the CE
  def buildTypeModel(workingModel: Map[Seq[String], String]): (Map[Seq[String], String], Map[Seq[String], String]) = {

    // "Seq#Equal" and "Seq#Contains" are not included as they resolve to Boolean and are thus not useful for the CE
    val seqOpNames = Set("Seq#Empty", "Seq#Singleton", "Seq#Range", "Seq#Append", "Seq#Index", "Seq#Take", "Seq#Drop", "Seq#Length")
    // "Set#Card", "Set#Subset" and "Set#Equal" are not included as they resolve to Boolean and are thus not useful for the CE
    val setOpNames = Set("Set#Empty", "Set#Singleton", "Set#UnionOne", "Set#Union", "Set#Intersection", "Set#Difference")

    // define output maps for the operations of sequences, sets,
    var seqOperations = Map[Seq[String], String]()
    var setOperations = Map[Seq[String], String]()
    // var maskAndHeapIdentifiers = Map[String, String]()

    // choose the operations corresponding to the types from the model received by boogie
    for ((k, v) <- workingModel) {
      if (seqOpNames.contains(k(0))) {
        seqOperations += (k -> v)
      } else if (setOpNames.contains(k(0))) {
        setOperations += (k -> v)
      }
    }

    (seqOperations, setOperations)
  }

  // a CE generator for sequences
  def detSequences(opMapping: Map[Seq[String], String]): Map[String, Seq[String]] = {
    var retMap = Map[String, Seq[String]]()
    var tempMap = Map[Seq[String], String]()
    for ((seqOp, seqName) <- opMapping) {
      if (seqOp(0) == "Seq#Length") {
        retMap += (seqOp(1) -> Seq.fill(seqName.toInt)("#undefined"))
      } else if (seqOp(0) == "Seq#Empty") {
        retMap += (seqName -> Seq())
      } else {
        tempMap += (seqOp -> seqName)
      }
    }
    for ((seqOp, seqName) <- tempMap) {
      if (seqOp(0) == "Seq#Singleton") {
        retMap += (seqName -> Seq(seqOp(1)))
        tempMap -= seqOp
      }
      if (seqOp(0) == "Seq#Range") {
        retMap += (seqName -> Seq.range(seqOp(1).toInt, seqOp(2).toInt).map(x => x.toString))
        tempMap -= seqOp
      }
    }
    var found = true
    while (found) {
      found = false
      for ((seqOp, seqName) <- tempMap) {
        if (seqOp(0) == "Seq#Append") {
          (retMap.get(seqOp(1)), retMap.get(seqOp(2))) match {
            case (Some(_), Some(_)) =>
              retMap += (seqName -> (retMap.get(seqOp(1)).get ++ retMap.get(seqOp(2)).get))
              tempMap -= seqOp
              found = true
            case (_, _) => //
          }
        } else if (seqOp(0) == "Seq#Take") {
          retMap.get(seqOp(1)) match {
            case Some(_) =>
              retMap += (seqName -> retMap.get(seqOp(1)).get.take(seqOp(2).toInt))
              tempMap -= seqOp
              found = true
            case None => //
          }
        } else if (seqOp(0) == "Seq#Drop") {
          retMap.get(seqOp(1)) match {
            case Some(_) =>
              retMap += (seqName -> retMap.get(seqOp(1)).get.drop(seqOp(2).toInt))
              tempMap -= seqOp
              found = true
            case None => //
          }
        } else if (seqOp(0) == "Seq#Index") {
          retMap.get(seqOp(1)) match {
            case Some(x) =>
              retMap += (seqOp(1) -> (x.updated(seqOp(2).toInt, seqName)))
              tempMap -= seqOp
              found = true
            case None => //
          }
        }
      }
    }
    retMap
  }

  // a CE generator for sets
  def detSets(opMapping: Map[Seq[String], String]): Map[String, Set[String]] = {
    var retMap = Map[String, Set[String]]()
    for ((seqOp, seqName) <- opMapping) {
      if (seqOp(0) == "Set#Empty") {
        retMap += (seqName -> Set())
      }
      if (seqOp(0) == "Set#Singleton") {
        retMap += (seqName -> Set(seqOp(1)))
      }
    }
    var tempMap = mutable.Map[Seq[String], String]()
    for ((seqOp, seqName) <- opMapping) {
      if (seqOp(0) == "Set#UnionOne") {
        tempMap += (seqOp -> seqName)
      }
    }
    while (!tempMap.isEmpty) {
      for ((seqOp, seqName) <- tempMap) {
        retMap.get(seqOp(1)) match {
          case Some(x) =>
            retMap += (seqName -> x.union(Set(seqOp(2))))
            tempMap -= seqOp
          case None => //
        }
      }
    }
    for ((seqOp, seqName) <- opMapping) {
      if (seqOp(0) == "Set#Union" || seqOp(0) == "Set#Difference" || seqOp(0) == "Set#Intersection") {
        tempMap += (seqOp -> seqName)
      }
    }
    while (!tempMap.isEmpty) {
      for ((seqOp, seqName) <- tempMap) {
        val firstSet = retMap.get(seqOp(1))
        val secondSet = retMap.get(seqOp(2))
        if ((firstSet != None) && (secondSet != None)) {
          if (seqOp(0) == "Set#Union") {
            retMap += (seqName -> firstSet.get.union(secondSet.get))
            tempMap -= seqOp
          } else if (seqOp(0) == "Set#Intersection") {
            retMap += (seqName -> firstSet.get.intersect(secondSet.get))
            tempMap -= seqOp
          } else if (seqOp(0) == "Set#Difference") {
            retMap += (seqName -> firstSet.get.diff(secondSet.get))
            tempMap -= seqOp
          }
        }
      }
    }
    retMap
  }

  // determine the identifier for the different Heap and Mask instances
  def oldAndReturnHeapMask(workingModel: Map[Seq[String], String]): Map[String, String] = {
    var resultMap = Map[String, String]()
    var oldHid = -1
    var retHid = -1
    var oldMid = -1
    var retMid = -1
    for ((k, v) <- workingModel) {
      if (k(0).startsWith("Heap")) {
        if (k(0).contains("@@")) {
          val curHid = k(0).stripPrefix("Heap@@").trim.toInt
          if (oldHid < curHid) {
            resultMap += ("OldHeap" -> v)
            oldHid = curHid
          }
        } else {
          val curHid = k(0).stripPrefix("Heap@").trim.toInt
          if (retHid < curHid) {
            resultMap += ("RetHeap" -> v)
            retHid = curHid
          }
        }
      } else if (k(0).startsWith("Mask")) {
        if (k(0).contains("@@")) {
          val curMid = k(0).stripPrefix("Mask@@").trim.toInt
          if (oldMid < curMid) {
            resultMap += ("OldMask" -> v)
            oldMid = curMid
          }
        } else {
          val curMid = k(0).stripPrefix("Mask@").trim.toInt
          if (retMid < curMid) {
            resultMap += ("RetMask" -> v)
            retMid = curMid
          }
        }
      }
    }
    if ((oldHid == -1) && (retHid != -1)) {
      resultMap += ("OldHeap" -> resultMap.get("RetHeap").get)
    } else if ((retHid == -1) && (oldHid != -1)) {
      resultMap += ("RetHeap" -> resultMap.get("OldHeap").get)
    }
    if ((oldMid == -1) && (retMid != -1)) {
      resultMap += ("OldMask" -> resultMap.get("RetMask").get)
    } else if ((retMid == -1) && (oldMid != -1)) {
      resultMap += ("RetMask" -> resultMap.get("OldMask").get)
    }
    // Pick the second to last Mask:
    //    for ((k, v) <- workingModel) {
    //      if (k(0).stripPrefix("Mask@").trim.toInt + 1 == newMask._1.stripPrefix("Mask@").trim.toInt) {
    //        resultMap += (v -> "MaskNewHeap")
    //      }
    //    }
    resultMap
  }

  def detHeapTypes(opMapping: Map[Seq[String], String]): Set[(String, (String, String), (String, String))] = {
    val heapMaskMap = oldAndReturnHeapMask(opMapping)
    var permMap = Map[String, String]()
    for ((key, value) <- opMapping) {
      if (key(0) == "U_2_real") {
        permMap += (key(1) -> value)
      }
    }

    var resSet = Set[(String, (String, String), (String, String))]()
    val oldMaskid = heapMaskMap.get("OldMask").get
    val retMaskid = heapMaskMap.get("RetMask").get
    for ((key, perm) <- opMapping) {
      if (key(0) == "MapType1Select") {
        val reference = key(2)
        val field = key(3)
        if (key(1) == oldMaskid) {
          opMapping.get(Seq("MapType0Select", heapMaskMap.get("OldHeap").get, reference, field)) match {
            case Some(v) => resSet += (("OldHeap", (reference, field), (v, permMap.get(perm).get)))
            case None => resSet += (("OldHeap", (reference, field), ("#undefined", permMap.get(perm).get)))
          }
        } else if (key(1) == retMaskid) {
          opMapping.get(Seq("MapType0Select", heapMaskMap.get("RetHeap").get, reference, field)) match {
            case Some(v) => resSet += (("RetHeap", (reference, field), (v, permMap.get(perm).get)))
            case None => resSet += (("RetHeap", (reference, field), ("#undefined", permMap.get(perm).get)))
          }
        }
      }
    }

    resSet
  }

  def evaluateHT(opMapping: Map[Seq[String], String], members: Map[String, String], heapTypes: Set[(String, (String, String), (String, String))], predicates: Set[String], fields: Set[String]): (Map[String, (String, String)], Map[String, (String, String)]) = {
    // choosing all the needed values from the Boogie Model
    var usedIdent = Map[String, String]()
    for ((key, value) <- opMapping) {
      if (key(0) == "null") {
        usedIdent += (value -> "null")
      }
      for (fie <- fields) {
        if (key(0) == fie || (key(0).startsWith(fie ++ "_") && !key.contains("@"))) {
          usedIdent += (value -> fie)
        }
      }
      for (pre <- predicates) {
        if (key(0) == pre) {
          for ((refName, refValue) <- members) {
            if (key(1) == refValue) {
              usedIdent += (value -> s"$pre($refName)")
            }
          }
        }
      }
    }

    // replacing all the identifiers with the names from the viper program
    var oldHeap = Map[String, (String, String)]()
    var retHeap = Map[String, (String, String)]()
    var tempHT = Set[(String, (String, String), (String, String))]()
    var tempRef = Map[String, String]()
    var added = false
    for ((heapInstance, (reference, field), (value, permission)) <- heapTypes) {
      usedIdent.get(reference) match {
        case Some("null") =>
          if (heapInstance == "OldHeap") {
            oldHeap += (usedIdent.get(field).get -> (value, permission))
          } else {
            retHeap += (usedIdent.get(field).get -> (value, permission))
          }
        case _ =>
          var found = false
          for ((refName, refValue) <- members) {
            if (refValue == reference) {
              found = true
              if (heapInstance == "OldHeap") {
                oldHeap += (refName ++ "." ++ usedIdent.get(field).get -> (value, permission))
              } else {
                retHeap += (refName ++ "." ++ usedIdent.get(field).get -> (value, permission))
              }
              if (value.startsWith("T@U!val!")) {
                tempRef += (value -> (refName ++ "." ++ usedIdent.get(field).get))
                added = true
              }
            }
          }
          if (!found) {
            tempHT += ((heapInstance, (reference, field), (value, permission)))
          }
      }
    }
    while (added) {
      added = false
      for ((heapInstance, (reference, field), (value, permission)) <- tempHT) {
        tempRef.get(reference) match {
          case Some(x) =>
            tempHT -= ((heapInstance, (reference, field), (value, permission)))
            if (heapInstance == "OldHeap") {
              oldHeap += (x ++ "." ++ usedIdent.get(field).get -> (value, permission))
            } else {
              retHeap += (x ++ "." ++ usedIdent.get(field).get -> (value, permission))
            }
            if (value.startsWith("T@U!val!")) {
              tempRef += (value -> (x ++ "." ++ usedIdent.get(field).get))
              added = true
            }
          case None => //
        }
      }
    }
    (oldHeap, retHeap)
  }

}