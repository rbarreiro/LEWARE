import LEWARE

def schema :=
  SchemaDef.new "caaty"
  [
    (
      "chatMessage",
      .tuple [.string, .string],
      .record [
        ("timestamp", .datetime),
        (
          "content",
          .sum [
            (
              "userMessage",
              .record [("text", .string)]
            ),
            (
              "form",
              .record [
              ]
            )
          ]
        )
      ]
    )
  ]


def server := #server [schema]{
  .dbService
    {
      name := "userMessage",
      args := [("message", .string), ("chatId", .string)],
      res := option .string,
      roles := .roles ["user", "admin"]
    }
    (
      .ldo {
        llet n <- now,
        llet u <- uuid,
        llet r_ <- insertIdValue @@ &chatMessage @@
          (.t2 @@ &chatId @@ &u) @@
          r{"timestamp" = &n, "content" = cons(userMessage, r{"text" = &message } ) },
        .iopure @@ none
      }
    )
}


def app := #app [server] {
    text @@ "ola"
}

#eval genApp app
--#eval deployApp "localhost" 6401 app
