import utils._

package object privacysafer {
  // A way to encode each techniques in the types system is with
  // labels. For each technique we define two traits that specify if the
  // data was transformed with or without the technique.
  sealed trait NotEncrypted
  sealed trait Encrypted

  class Id {
    sealed abstract class IdData
    final case class Raw() extends IdData with NotEncrypted
    final case class AESECS[+T <: Data with NotEncrypted](data: T)
        extends IdData with Encrypted

    // Refer all kind of Data without considering path dependency.
    type Data = Id#IdData

    def encrypt[T <: Data with NotEncrypted](d: T): AESECS[T] = AESECS(d)
    def decrypt[T <: Data with NotEncrypted](d: AESECS[T]): T = d.data
  }
}

import privacysafer._

object Alice extends Id

object Bob extends Id

// Encryption tests from Alice and Bob.
object EncryptionTests {
  // Alice is the owner of the Data
  val aliceData: Alice.IdData = Alice.Raw()
  val aliceRawData: Alice.Raw = Alice.Raw()
  val aliceEncData: Alice.AESECS[Alice.Raw] = Alice.encrypt(aliceRawData)
  val aliceDecData: Alice.Raw = Alice.decrypt(aliceEncData)

  // Bob cannot be the owner of the Data
  illTyped("""
  val bobData: Bob.IdData = Alice.Raw()
  """)
  illTyped("""
  val bobRawData: Bob.Raw = Alice.Raw()
  """)
  illTyped("""
  val bobEncData: Bob.AESECS[Alice.Raw] = Alice.encrypt(aliceRawData)
  """)
  illTyped("""
  val encBobData: Alice.AESECS[Bob.Raw] = Alice.encrypt(aliceRawData)
  """)
  illTyped("""
  val bobDecData: Bob.Raw = Alice.decrypt(aliceEncData)
  """)

  // `Id' cannot encrypt already encrypted data
  illTyped("""
  (new Id).encrypt(aliceEncData)
  """)

  // `Id' cannot decrypt data encrypted by another Id.
  illTyped("""
  (new Id).decrypt(aliceEncData)
  """)
}

// Now we construct a Cloud which offers three services: (1) storing
// data in the Cloud, (2) Reading data from the Cloud and (3)
// Processing data and generate a Chart. The third service uses an
// internal service called `genChart' and `genChart' cannot process
// encrypted data.
//
// In a first version, called `DummyCloud', we don't add specific
// constraint on the type system. We show that this leads to an
// undesirable program that type checks.
object DummyCloud extends Id {
  case class Key()
  case class Chart() extends IdData

  // Stores a data and returns an accessor.
  def store(d: Data): Key = ???

  // Takes a data accessor and returns a data.
  def read(k: Key): Data = ???

  // Chart generator that takes any kind of Data. This method is
  // private and should be call from `processData'.
  private def genChart(d: Data): Chart = ???

  // Returns a chart from a data accessor.
  def processData(k: Key): Chart = genChart(read(k))

  // Test that stores Alice's raw and encrypted data and processes it.
  //
  // The process type checks with raw and encrypted data which is not
  // exactly what we want. We want that `genChart' only processes non
  // encrypted data and thus, type checks only in the presence of non
  // encrypted data.
  object DummyCloudTests {
    // Storing of Raw and Encrypted data
    val rawDataKey = DummyCloud.store(Alice.Raw())
    val encDataKey = DummyCloud.store(Alice.encrypt(Alice.Raw()))

    // Type checks with raw data -- Great!
    DummyCloud.processData(rawDataKey)

    // Type checks with encrypted data -- D'oh!
    DummyCloud.processData(encDataKey)
  }
}

// In a second version of the Cloud, called `SmarterCloud', we add a
// `NotEncrypted' constraint on the data of `genChart'. The constraint
// leads to the coercion of data of `processData' to be `NotEncrypted'.
//
// As we show in the test part, this solution excludes program that
// calls `processData' with encrypted data.
object SmarterCloud extends Id {
  // T encode the type of the stored data
  case class Key[T]()
  case class Chart() extends IdData

  // Stores a data and returns a parametric accessor. The parametric
  // accessor is parameterized with the type of the data.
  def store[T <: Data](d: T): Key[T] = ???

  // Takes a data accessor and returns a data of types of the
  // accessor's parameters.
  def read[T <: Data](k: Key[T]): T = ???

  // Chart generator that takes only non encrypted data. See the
  // `NotEncrypted' in the data declaration.
  private def genChart[T <: Data with NotEncrypted](d: T): Chart = ???

  // Doesn't type checks: the `T' should be a `NotEncrypted'
  illTyped("""
  def processData[T <: Data](k: Key[T]): Chart = genChart(read(k))
  """)

  // Returns a chart from a data accessor. Here the notation `with
  // NotEncrypted' is mandatory by the type system.
  def processData[T <: Data with NotEncrypted](k: Key[T]): Chart =
    genChart(read(k))

  // The test stores Alice's raw and encrypted data and then processes
  // it. The program type checks only with raw data.
  object SmarterCloudTests {
    // The key identifies the shape and the owner of stored data
    val aliceRawDataKey: Key[Alice.Raw] =
      SmarterCloud.store(Alice.Raw())
    val aliceEncDataKey: Key[Alice.AESECS[Alice.Raw]] =
      SmarterCloud.store(Alice.encrypt(Alice.Raw()))

    // Thus, Bob couldn't claim to be the owner of a Alice stored
    // information.
    illTyped("""
    val bobRawDataKey: Key[Bob.Raw] =
    SmarterCloud.store(Alice.Raw())
    """)
    illTyped("""
    val bobEncDataKey: Key[Bob.AESECS[Alice.Raw]] =
    SmarterCloud.store(Alice.encrypt(Alice.Raw()))
    """)
    illTyped("""
    val encBobDataKey: Key[Alice.AESECS[Bob.Raw]] =
    SmarterCloud.store(Alice.encrypt(Alice.Raw()))
    """)

    // Calling `processData' with raw data type checks - Great!
    SmarterCloud.processData(aliceRawDataKey)

    // Calling `processData' with encrypted data doesn't type check -
    // Great!
    illTyped("""
    SmarterCloud.processData(aliceEncDataKey)
    """)
  }
}

// The previous version is OK but rejects program that calls
// `processData' with encrypted data even if the data owner decrypts
// the data.
//
// In the last version, we organize the program in the way of *pulled
// functionalities*. The `genChart' method is now public but still
// cannot take encrypted data. The `processData' method is now
// executed at Alice's side where she decrypts her data before
// calling the `genChart' method.
object PullableCloud extends Id {
  case class Key[T]()
  case class Chart() extends IdData

   def store[T <: Data](d: T): Key[T] = ???
   def read[T <: Data](k: Key[T]): T = ???

  // Chart generator that takes only non encrypted data is now public.
  def genChart[T <: Data with NotEncrypted](d: T): Chart = ???

  // Alice pulls the `processData' functionality. If the data is
  // encrypted, first Alice decrypts it and then calls `genChart'.
  object PullerAlice extends Id {
    import scala.reflect.runtime.universe._

    def processData[T <: IdData : TypeTag](k: Key[T]): Chart =
      PullableCloud.read(k) match {
        case d: IdData with NotEncrypted =>
          PullableCloud.genChart(d)
        case e: AESECS[IdData with NotEncrypted] @unchecked
            if typeOf[T] =:= typeOf[IdData with NotEncrypted] =>
          PullableCloud.genChart(decrypt(e))
      }
  }

  // The test stores Alice's and Bob's raw and encrypted data and then
  // processes it. The program type checks with Alice's raw and
  // encrypted data. It doesn't type checks if Alice tries to generate
  // a chart from Bob data.
  object PullerTests {
    val aliceRawDataKey =
      PullableCloud.store(PullerAlice.Raw())
    val aliceEncDataKey =
      PullableCloud.store(PullerAlice.encrypt(PullerAlice.Raw()))

    // Alice can process raw and encrypted data
    PullerAlice.processData(aliceRawDataKey)
    PullerAlice.processData(aliceEncDataKey)

    // Alice cannot process Bob data.
    val bobRawDataKey =
      PullableCloud.store(Bob.Raw())
    val bobEncDataKey =
      PullableCloud.store(Bob.encrypt(PullerAlice.Raw()))

    illTyped("""
    PullerAlice.processData(bobRawDataKey)
    """)
    illTyped("""
    PullerAlice.processData(bobEncDataKey)
    """)
  }
}
