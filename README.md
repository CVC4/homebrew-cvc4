# Homebrew tap for CVC4

This repository is the [homebrew](https://brew.sh/) tap of CVC4. To install
CVC4 using this tap, use the following commands:

```
$ brew tap cvc4/cvc4
$ brew install cvc4/cvc4/cvc4 [--HEAD] [--with-java-bindings]
```

The CVC4 formula supports the following optional arguments:

- `--HEAD`: Builds the current master branch of CVC4
- `--with-java-bindings`: installs the Java bindings for CVC4
- `--with-readline`: installs optional Readline support for improved
  text-editing support in interactive mode. Requires the `with-gpl` option
- `--with-gpl`: Permit GPL dependences, if available

## Using the Java bindings

The following instructions assume that CVC4 is installed with the Java bindings
and demonstrate how to compile a single Java file that uses the bindings. Adapt
as needed for larger projects.  To use the Java bindings, add `
/usr/local/share/java/CVC4.jar` to the classpath when compiling the program:

```
$ javac -cp /usr/local/share/java/CVC4.jar Foo.java
```

To run the program, add `CVC4.jar` and the path of `Foo.class` to your
classpath and set `java.library.path` to the location of `libcvc4jni` (should
be `/usr/local/lib/jni` if CVC4 was installed with homebrew):

```
$ java -cp /usr/local/share/java/CVC4.jar:<path_to_class_file> -Djava.library.path=/usr/local/lib/jni <class_to_run>
```
