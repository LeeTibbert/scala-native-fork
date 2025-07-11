#!/usr/bin/env bash

set -e

nativelib=nativelib/src/main
scala=scala
scalaNext=scala-next
unsafe=scala/scalanative/unsafe
unsigned=scala/scalanative/unsigned
runtime=scala/scalanative/runtime
javaNIO=javalib/src/main/scala/java/nio
javaUtil=javalib/src/main/scala/java/util

sharedTest=unit-tests/shared/src/test

javalibTestJDK9=${sharedTest}/require-jdk9/org/scalanative/testsuite/javalib
javalibTestJDK11=${sharedTest}/require-jdk11/org/scalanative/testsuite/javalib

function gyb() {
  file=$1
  if [ ${file: -4} == ".gyb" ]; then
    outputFile="${file%.gyb}"
    echo "Generate $outputFile"
    scripts/gyb.py --line-directive '' -o "$outputFile" "$file"
  else 
    echo "$file is not a .gyb file"
    exit 1
  fi
}

gyb_files() {
  local lib="$1"
  local scalaVersion="$2"
  local package="$3"
  shift 3
  for name in "$@"; do
      gyb "$lib/$scalaVersion/$package/$name.scala.gyb"
  done
}

gyb_files $nativelib $scala $unsafe Tag Nat CStruct CFuncPtr Size
gyb_files $nativelib $scala $unsigned USize
gyb_files $nativelib $scala $runtime Arrays Boxes Primitives

gyb clib/src/main/scala/scala/scalanative/libc/stdatomic.scala.gyb
gyb clib/src/main/resources/scala-native/stdatomic.c.gyb

gyb $javaNIO/Buffers.scala.gyb
gyb $javaNIO/HeapBuffers.scala.gyb
gyb $javaNIO/HeapByteBufferViews.scala.gyb
gyb $javaNIO/MappedByteBufferViews.scala.gyb
gyb $javaNIO/PointerByteBufferViews.scala.gyb

gyb $javaUtil/ArraysJDK9Methods.scala.gyb

gyb unit-tests/native/src/test/scala/org/scalanative/testsuite/niobuffer/ByteBufferViewsNativeTests.scala.gyb
gyb unit-tests/shared/src/test/scala/org/scalanative/testsuite/javalib/nio/BufferAdapter.scala.template.gyb

gyb ${javalibTestJDK9}/util/ArraysOfAnyValTestOnJDK9.scala.gyb
gyb ${javalibTestJDK11}/nio/BuffersMismatchTestOnJDK11.scala.gyb
